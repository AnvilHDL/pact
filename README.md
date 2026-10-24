<p align="center">
  <a href="https://anvil.kisp-lab.org/" aria-label="AnvilHDL website">
    <picture>
      <img alt="Pact" src="docs/logo/pact-horizontal.png" height="84">
    </picture>
  </a>
</p>

# An Extension of AnvilHDL with a Type System for Communication Safety

[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.23301148.svg)](https://doi.org/10.5281/zenodo.23301148)

**Pact** extends [AnvilHDL](https://github.com/AnvilHDL/anvil), a timing-safe hardware description language, with **session types** for the communication between components.
- Each component declares its protocol as an *interface*: which messages it sends and receives, in what order, and with what timing.
- Components are wired together in a *pool*.
- The compiler checks that every process follows its declared protocol, and that the components in each pool are *compatible*.

Compatible components keep making progress. Similar to Anvil's the checks are compile-time and the designs compile to SystemVerilog.

> **Note** Pact is described in [**A Type System for Communication-Safe Hardware Design**](https://arxiv.org/abs/2610.26599), conditionally accepted to POPL 2027.
> Pact builds on AnvilHDL, whose type system and timing contracts are described in [**Anvil: A General-Purpose Timing-Safe Hardware Description Language**](https://doi.org/10.1145/3779212.3790125) (ASPLOS 2026).

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

> [!IMPORTANT]
> **The documentation will be released soon.** Until then, please see [session_examples](session_examples/README.md) for a list of examples.

A memory serves a writer and a reader. The memory and the writer declare their protocols as interfaces. The reader declares none, so its type is inferred:

```anvil
struct write_t { addr : logic[8], data : logic[8] }

chan read_ch  { right req : (logic[8]@#1), left res : (logic[8]@#1) }
chan write_ch { left req : (write_t@#1) }

// Each cycle the memory takes a read, a write, both, or neither; a read is answered a cycle later.
interface mem_intfc (rd : right read_ch, wr : left write_ch) =
    ⋀(#rd.req : #1 ; #rd.res, #wr.req : #1, *) ; #1

// The writer writes on some cycles and idles on others; both happen infinitely often.
interface writer_intfc (wr : right write_ch) = (wr.req ++ #1) ; #1

proc memory (mem_intfc) {
    reg mem : logic[256][8];
    reg rd_data : logic[8];
    loop {
        offer {
            addr = irecv rd.req => (
                set rd_data := *mem[addr] >>
                isend rd.res(*rd_data)
            ),
            w = irecv wr.req => set mem[w.addr] := w.data
        } else {
            ()
        } >>
        cycle 1
    }
}

proc writer (writer_intfc) {
    reg n : logic[8];
    reg turn : logic;
    loop {
        fair if (*turn) {
            send wr.req(write_t::{addr = *n; data = *n + 8'd100})
        } else {
            cycle 1
        } >>
        {
            set n := *n + 8'd1;
            set turn := ~*turn
        }
    }
}

// No interface: the reader's type is inferred from its body.
proc reader (rd : left read_ch) {
    reg addr : logic[8];
    loop {
        send rd.req(*addr) >>
        let v = recv rd.res >>
        dprint "mem[%d] = %d\n" (*addr, v) >>
        set addr := *addr + 8'd1
    }
}

pool mem_pool {
    rd_le -- rd_ri : read_ch,
    wr_le -- wr_ri : write_ch;
    imem : mem_intfc(rd_ri, wr_le),
    iwriter : writer_intfc(wr_ri),
    ireader : proc reader(rd_le)
}

proc top () {
    pool p : mem_pool;
    spawn memory[p.imem];
    spawn writer[p.iwriter];
    spawn p.ireader;
    loop { cycle 1 }
}
```

The compiler checks each process against its interface, infers the reader's type, and checks that the three components are compatible:

```text
$ dune exec pact -- -just-check -verbose top.anvil
[info] Session check passed for process memory thread 0
[info] Session check passed for process writer thread 0
[info] Inferred type of process reader: rd.req;rd.res;#<1>
[info] Compatibility check passed for pool instance p in process top
```

The example uses:
- a conjunctive offer `⋀(...)`: in one cycle the memory takes a read, a write, both, or neither (`*`), with `#m` marking an exchange completed within the cycle;
- delays `#n`: a read is answered one cycle after its request;
- a fair choice `++`, matched by `fair if` in the writer: writing and idling must both recur, an annotation of the designer's intent that the checker uses;
- a process as a pool member: `ireader : proc reader(rd_le)` has no interface, its type is inferred, and `spawn p.ireader` spawns it on the member's endpoints, while interface members are spawned with `spawn memory[p.imem]`.

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

The Unicode forms `⨁`, `⋀`, `∑`, `∏`, `μ` and `∀` are also accepted. The fair constructs are annotations of intent: in processes, the programmer writes `fair if` and `fair xoffer` to match them.

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

  - **Found a bug or need a feature?** [Open an Issue](https://github.com/AnvilHDL/Pact/issues/new)
  - **Want to contribute?** [Submit a Pull Request](https://github.com/AnvilHDL/Pact/compare)
  - **Issues in the underlying AnvilHDL language** can also be reported [upstream](https://github.com/AnvilHDL/anvil/issues).

-----

## Citing

If you use Pact, please cite:

```text
A. R. Jha, J. Z. Yu, U. Mathur, and P. Saxena, “A type system for communication-safe hardware design,” Proceedings of the ACM on Programming Languages, no. POPL, 2027. Conditionally accepted. [Online]. Available: https://arxiv.org/abs/2610.26599
```

or in BibTeX format:

```bibtex
@article{Jhacommunicationsafehardware2027,
   title={A Type System for Communication-Safe Hardware Design},
   author={Jha, Aditya Ranjan and Yu, Jason Zhijingcheng and Mathur, Umang and Saxena, Prateek},
   journal={Proceedings of the ACM on Programming Languages},
   year={2027},
   number={POPL},
   url={https://arxiv.org/abs/2610.26599},
   note={Conditionally accepted. Preprint available at arXiv:2610.26599}
}
```

The paper's artifact (this compiler, the benchmarks and the Lean mechanization) is archived on Zenodo: [10.5281/zenodo.23301148](https://doi.org/10.5281/zenodo.23301148).

Pact builds on AnvilHDL. To cite the underlying language, please use:

```text
J. Z. Yu, A. R. Jha, U. Mathur, T. E. Carlson, and P. Saxena, “Anvil: a general-purpose timing-safe hardware description language,” in Proceedings of the 31st ACM international conference on architectural support for programming languages and operating systems, volume 2, in ASPLOS ’26. Pittsburgh, PA, USA: Association for Computing Machinery, 2026, pp. 110–136. doi: 10.1145/3779212.3790125
```

or in BibTeX format:

```bibtex
@inproceedings{yu2026anvil,
   title={Anvil: A General-Purpose Timing-Safe Hardware Description Language},
   author={Yu, Jason Zhijingcheng and Jha, Aditya Ranjan and Mathur, Umang and Carlson, Trevor E and Saxena, Prateek},
   year={2026},
   publisher={Association for Computing Machinery},
   booktitle={Proceedings of the 31st ACM International Conference on Architectural Support for Programming Languages and Operating Systems, Volume 2},
   series={ASPLOS '26},
   address={Pittsburgh, PA, USA},
   pages={110--136},
   doi={10.1145/3779212.3790125}
}
```

## Discussion

We would love to hear your feedback!
Please join https://anvilhdl.zulipchat.com/ for discussions.

> **Acknowledgement**: We want to thank [**Zulip**](https://zulip.com/)
> for sponsoring the community chat channel and enabling discussions.
> Zulip is an organized team chat app designed for efficient communication.
