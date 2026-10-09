<p align="center">
  <a href="https://anvil.kisp-lab.org/" aria-label="AnvilHDL website">
    <picture>
      <img alt="Pact" src="docs/logo/pact-horizontal.png" height="84">
    </picture>
  </a>
</p>

# An Extension of AnvilHDL with a Type System for Communication Safety

**Pact** extends [AnvilHDL](https://github.com/jasonyu1996/anvil), a timing-safe hardware description language, with **session types** for the communication between components.
- Each component declares its protocol as an *interface*: which messages it sends and receives, in what order, and with what timing.
- Components are wired together in a *pool*.
- The compiler checks that every process follows its declared protocol, and that the components in each pool are *compatible*.

Compatible components never deadlock, never wait for a message that cannot arrive, and keep making progress. This holds under the fairness the designer declares. The checking happens at compile time, on top of Anvil's timing-safety guarantees. Designs compile to SystemVerilog.

> **Note** Pact builds on AnvilHDL, whose type system and timing contracts are described in [**Anvil: A General-Purpose Timing-Safe Hardware Description Language**](https://arxiv.org/abs/2503.19447) (ASPLOS 2026).

-----

## Design Goals

Pact keeps AnvilHDL's guarantees and adds safety for communication between components:

| Feature | Description |
| :--- | :--- |
| **Communication safety** | Session types describe each component's protocol: the order of messages, choices between them, offers, recursion and parallel threads. The compiler checks that each process conforms to its type, and that composed components are compatible, so that no component deadlocks or starves. |
| **Timing safety** | Inherited from AnvilHDL. Any value referenced across cycles is guaranteed to be **stable** and **meaningful**, preventing mistakes such as using a value before it is ready. |
| **Composability** | Both guarantees hold across module boundaries. Components can be checked against their interfaces and composed with confidence, without inspecting each other's implementation. |
| **Expressiveness** | Safety comes from the type system, not from hiding the hardware. Registers, wires and clock cycles stay explicit, and protocols can be written with cycle-level precision. Exchanges are either blocking (`send`, `recv`) or completed within the cycle (`isend`, `irecv`). |

-----

## A First Example

Two components exchange a request, a reset and an acknowledgement over the channel `ch`. Each declares its side of the protocol, and the pool connects them:

```anvil
chan ch {
    left req : (logic@#1),
    left reset : (logic@#1),
    right ack : (logic@#1)
}

// foo1 sends req, waits 4 cycles, sends reset at once, then receives ack.
interface foo1_intfc (ep : right ch) = ep.req ; #4 ; #ep.reset ; ep.ack ; #1
interface foo2_intfc (ep : left ch)  = ep.req ; ep.reset ; ep.ack ; #1

proc foo1 (foo1_intfc) {
    loop {
        send ep.req(1'd1) >>
        cycle 4 >>
        isend ep.reset(1'd0) >>
        let ack = recv ep.ack >>
        cycle 1
    }
}

proc foo2 (foo2_intfc) {
    loop {
        let req = recv ep.req >>
        let reset = recv ep.reset >>
        send ep.ack(1'd1) >>
        cycle 1
    }
}

pool compat_pool {
    ep_le -- ep_ri : ch;
    i1 : foo1_intfc(ep_ri),
    i2 : foo2_intfc(ep_le)
}

proc top () {
    pool p : compat_pool;
    spawn foo1[p.i1];
    spawn foo2[p.i2];
    loop { cycle 1 }
}
```

The compiler checks that each process follows its interface, then checks that the two interfaces are compatible:

```text
$ dune exec pact -- -just-check -verbose top.anvil
[info] Session check passed for process foo1 thread 0
[info] Session check passed for process foo2 thread 0
[info] Compatibility check passed for pool instance p in process top
```

If `foo2` waited for `ack` before `reset`, each side would wait on the other, and the compatibility check would reject the pool. A longer version of this example is in [`session_examples/test_compatiblity.anvil`](session_examples/test_compatiblity.anvil).

### Session types at a glance

| Construct | Meaning |
| :--- | :--- |
| `ep.m`, `#ep.m` | Exchange message `m`, blocking, or completed within the cycle |
| `#n` | Wait `n` cycles |
| `s1 ; s2` | Sequence |
| `s1 + s2`, `s1 ++ s2` | Internal choice; `++` is fair: if the choice recurs, both branches recur |
| `&(...)`, `^(...)`, `^^(...)` | Offer one or more messages, an exclusive offer, and a fair exclusive offer |
| `s1 \|\| s2` | Parallel threads |
| `rec X . s`, `F s` | Recursion; `F s` means `s` eventually happens |

The Unicode forms `⨁`, `⋀`, `∑`, `∏`, `μ` and `∀` are also accepted. In processes, `fair if` and `fair xoffer` correspond to the fair constructs.

### New to AnvilHDL?

Pact is a superset of AnvilHDL, so Anvil's resources teach the base language:
- the [**Online Playground**](https://anvil.kisp-lab.org/), with no installation needed;
- a [**Short Tutorial with interactive examples**](https://docs.anvil.kisp-lab.org/helloWorld.html);
- the [**AnvilHDL Docs**](https://docs.anvil.kisp-lab.org/).

-----

## Local Installation

### Prerequisites

- **OCaml**: Version 5.2.0
- **Verilator**: Version 5.024 (Required for software simulation)
- **Opam**: [Installation Guide](https://opam.ocaml.org/)

### Build Instructions

Clone the repository and install dependencies:

```bash
# Install dependencies
opam install . --deps-only

# Build the project
eval $(opam env) && dune build  # or for release build: dune build --release
```

This builds the `pact` compiler locally.

For global installation, you can run:

```bash
# To install the pact binary globally
opam install .

# To uninstall
opam uninstall .

# To update the binary to the latest commits (HEAD)
opam reinstall .
```

-----

## Compiler Usage

Run the compiler using `dune`. **Note**: For a global installation, replace `dune exec pact --` with `pact`.

```bash
dune exec pact -- [OPTIONS] <source-file>
```

**Common Options:**

  - `-just-check`: Only type-check the source file without generating code.
  - `-o <output-file>`: Specify output file name.
  - `-O <opt-level>`: Specify optimization level: 0, 1, 2 (default) or 3.
  - `-verbose`: Show progress and write debug logs (automata, products, counterexamples) to `./logs/<input>/`.
  - `-log-dir <dir>`: Write debug logs to the given directory.
  - `-silent`: Write compatibility traces to the log directory and keep the terminal output short.
  - `-json`: Output compilation results in JSON format.
  - `-ast`: With `-json`, check the input and include its AST, used by the language server.
  - `-disable-lt-checks`: Disable lifetime-related checks.
  - `-strict-dtc`: Enable strict data type checks (prevents abstract data types conversion).
  - `-help`: Display all options.

**Session-type and compatibility options:**

  - `-infer`: Check compatibility with the types inferred from the spawned processes instead of the declared interfaces.
  - `-debug-choice <n>`: Run only the compatibility check, with a chosen checker. Compilation itself always uses the fast check.
    - `2` is the fast check.
    - `3` is the cycle-accurate simultaneous check.
    - `5` and `6` are the same two checks on inferred types.
  - `-j <n>`: Use `n` cores to build compatibility products.
  - `-disable-compat-checks`: Skip pool compatibility checks.
  - `-disable-session-checks`: Skip all session-type checks.

### Running Examples

General designs are in the `examples` directory, and session-typed designs with pools in `session_examples`. Ensure Verilator is in your `$PATH`.

```bash
cd examples

# Build a specific module (defaults to 'top' if unspecified)
make MODULE_NAME=<name>

# Build with tracing enabled
# After simulation, you can find the waveform at logs/trace.vcd
make MODULE_NAME=<name> TRACE_ON=1

# Simulate the design
make run MODULE_NAME=<name> TIMEOUT=1000

# Clean up build artifacts
make clean
```

### Running Tests

```bash
# Run all tests
python3 run-tests.py

# Run specific test suites
cd examples
sh typecheck-test.sh   # Type checking tests
bash test-all.sh       # Simulation tests
```

-----

## Editor Support

- **[Pact Language Server](https://github.com/AnvilHDL/Pact-LSP)**:
  - diagnostics, including session-type and compatibility errors;
  - completion and hover help for Pact syntax;
  - navigation across interfaces, pools and processes;
  - the remaining session type at each step.

  It has VS Code and Vim/Neovim extensions.
- **[VS Code syntax highlighting](editors/vscode/README.md)**: the TextMate grammar on its own.

-----

## Contributing

Pact is **experimental** and under active development. We welcome feedback and contributions!

  - **Found a bug or need a feature?** [Open an Issue](https://github.com/arj4web/Pact/issues/new)
  - **Want to contribute?** [Submit a Pull Request](https://github.com/arj4web/Pact/compare)
  - **Issues in the underlying AnvilHDL language** can also be reported [upstream](https://github.com/jasonyu1996/anvil/issues).

-----

## Citing

Pact builds on AnvilHDL. To cite the underlying language, please use:

```text
J. Z. Yu, A. R. Jha, U. Mathur, T. E. Carlson, and P. Saxena, “Anvil: a general-purpose timing-safe hardware description language,” in Proceedings of the 31st ACM international conference on architectural support for programming languages and operating systems, in ASPLOS ’26. Pittsburgh, PA, USA: Association for Computing Machinery, 2026. [Online]. Available: https://arxiv.org/abs/2503.19447
```

or in BibTeX format:

```bibtex
@inproceedings{yu2026anvil,
   title={Anvil: A General-Purpose Timing-Safe Hardware Description Language},
   author={Yu, Jason Zhijingcheng and Jha, Aditya Ranjan and Mathur, Umang and Carlson, Trevor E and Saxena, Prateek},
   year={2026},
   publisher={Association for Computing Machinery},
   booktitle={Proceedings of the 31st ACM International Conference on Architectural Support for Programming Languages and Operating Systems},
   series={ASPLOS '26},
   address={Pittsburgh, PA, USA},
   url={https://arxiv.org/abs/2503.19447},
   note={To appear. Preprint available at arXiv:2503.19447}
}
```

## Discussion

We would love to hear your feedback!
Please join https://anvilhdl.zulipchat.com/ for discussions.

> **Acknowledgement**: We want to thank [**Zulip**](https://zulip.com/)
> for sponsoring the community chat channel and enabling discussions.
> Zulip is an organized team chat app designed for efficient communication.
