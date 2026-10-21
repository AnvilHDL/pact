# Pact Session Examples

This directory contains Pact examples for session types, offers, pools and compatibility checking. The examples are grouped by what they demonstrate.

---

## Running the Examples

```bash
# Type-check an example, including the compatibility of the pools its processes instantiate
dune exec pact -- -just-check -verbose <example>.anvil

# Check every pool in a file, including pools no process instantiates
dune exec pact -- -just-check -debug-choice 3 <example>.anvil   # simultaneous check
dune exec pact -- -just-check -debug-choice 2 <example>.anvil   # fast check, closed pools only

# Build and simulate an example (AnvilHDL + Verilator)
make MODULE_NAME=<example> run

# Clean all build artifacts
make clean
```

Makefile flags: `COMPATOFF=1` skips compatibility checks, `LTOFF=1` skips lifetime checks, `DEBUG=1` adds `-verbose`, and `NOOPT=1` compiles at `-O 0`.

The *Result* column is the outcome of `-just-check`. Pools that no process instantiates are checked only with `-debug-choice`.

---

## Pools and Compatibility

### Two components

| Example | Features | Result |
| --- | --- | --- |
| [test_compatiblity](test_compatiblity.anvil) | The README's first example: request, reset and acknowledgement over one channel | compatible |
| [test_deadlock](test_deadlock.anvil) | Each side waits for the other first | incompatible |
| [test_process_member](test_process_member.anvil) | A process as a pool member (`i1 : proc foo1(ep_ri)`), its type inferred; `spawn p.i1` | compatible |
| [test_wildcard_top](test_wildcard_top.anvil) | A conjunctive offer with an else arm against a delayed peer | compatible |
| [test_fifo](test_fifo.anvil) | FIFO with fair choices and `F` | compatible |

### Several components

| Example | Features | Result |
| --- | --- | --- |
| [test_base_multiparty](test_base_multiparty.anvil) | Three processes relay a request around a ring | compatible |
| [test_process_member_multiparty](test_process_member_multiparty.anvil) | The same ring with every member a process; `spawn p.i1` for each | compatible |
| [test_diner_philosopher](test_diner_philosopher.anvil) | Three processes in a ring with a cyclic wait (dining philosophers) | incompatible |
| [test_offer_choice_compatiblity](test_offer_choice_compatiblity.anvil) | An internal choice of message order met by an exclusive offer | compatible |
| [test_offer_choice_multiparty](test_offer_choice_multiparty.anvil) | A third component chooses the order, sent as data | compatible |

### Pools checked with `-debug-choice`

| Example | Features |
| --- | --- |
| [test_positive_compat](test_positive_compat.anvil) | Pools of inline types expected to be compatible (`// true`) |
| [test_negative_compat](test_negative_compat.anvil) | Pools of inline types expected to be incompatible (`// false`) |
| [test_types](test_types.anvil) | Inline member types: choice, conjunctive offer, `F`, parallel |
| [open_phase_channel_params](open_phase_channel_params.anvil) | An open pool: a relay with one side left to the environment |
| [test_ace](test_ace.anvil) | ACE cache-coherence controller as inline types |
| [test_axi](test_axi.anvil) | AXI read path: arbiter, FIFO, spill register and mux stages |

---

## Session Types for Processes

### Conjunctive offers (`offer`, `⋀`)

| Example | Features | Result |
| --- | --- | --- |
| [test_and_top](test_and_top.anvil) | Instant receives with different delays and an else arm | ok |
| [tryand_top](tryand_top.anvil) | `offer` over two receives, driven by a test process | ok |
| [test_nested_and](test_nested_and.anvil) | Offers nested inside offer arms | ok |
| [memory](memory.anvil) | Memory serving reads and writes in one offer; a read answers with `F` | ok |
| [top2](top2.anvil) | `offer` over two receives | ok |
| [offer_conjunction](offer_conjunction.anvil) | An exclusive offer with a conjunction arm | ok |

### Exclusive offers (`xoffer`, `⨁`)

| Example | Features | Result |
| --- | --- | --- |
| [test_xor_top](test_xor_top.anvil) | Instant receives with different delays and an else arm | ok |
| [test_ex_choice_top](test_ex_choice_top.anvil) | Blocking exclusive offer | ok |
| [tryxor](tryxor.anvil) | `xoffer` over two receives, driven by a test process | ok |
| [try_wildcard](try_wildcard.anvil) | Else arm with its own delay | ok |
| [test_try_send](test_try_send.anvil) | `try` receive with an else arm | ok |
| [top](top.anvil) | `xoffer` over two receives | ok |

### Choices, recursion and parallel threads

| Example | Features | Result |
| --- | --- | --- |
| [test_choice_top](test_choice_top.anvil) | Internal choice (`+`) and `F` | ok |
| [test_choice_nested_top](test_choice_nested_top.anvil) | Nested choices under `F` | ok |
| [test_local_top](test_local_top.anvil) | Two processes on a local channel, `F` on the waiting side | ok |
| [test_nested_rec](test_nested_rec.anvil) | Recursion inside a type (`μ X`) | ok |
| [test_parallel_top](test_parallel_top.anvil) | Parallel threads receiving different messages (`\|\|`) | ok |
| [test_multiprotocol](test_multiprotocol.anvil) | One process implementing two interfaces | ok |

### Handshakes

| Example | Features | Result |
| --- | --- | --- |
| [test_readyack_top](test_readyack_top.anvil) | Request and response with blocking handshakes | ok |
| [test_dual_handshake](test_dual_handshake.anvil) | An offer mixing a send with two receives | ok |
| [test_comb_loop](test_comb_loop.anvil) | An offer with a send arm and a receive arm | ok |

---

## Type Syntax and Automata

| Example | Features |
| --- | --- |
| [test_automata_construction](test_automata_construction.anvil) | Small types for checking automaton construction: instant actions, parallel, conjunctive offers, recursion |
| [type_aesthetics](type_aesthetics.anvil) | Quantified types: `∀`, `∏`, `∑`, exclusions, nested quantifiers |

> **Total:** 39 examples
