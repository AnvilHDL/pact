# Session Type Checking Implementation

## Overview

This document describes the session type checking implementation for the Anvil compiler, which verifies that event graphs conform to specified session types (communication protocols).

## Session Type Constructs

Session types in Anvil support the following constructs (defined in `lib/lang.ml`):

1. **`StyAtom`** - Single atomic action (message send/receive or delay)
2. **`StySeq`** - Sequential composition (s1 ; s2)
3. **`StyChoice`** - Internal choice (s1 + s2) - either branch can be taken
4. **`StyParallel`** - Parallel composition (s1 || s2) - both branches execute concurrently
5. **`StyFuture`** - Future operator (F s) - session will be satisfied eventually
6. **`StyChoiceDual`** - External choice (NOT YET SUPPORTED)

## Event Graph Mapping

### Branching Constructs

The event graph can represent branching through:

1. **Internal Choice (`StyChoice`)**: Represented by `Branch` event sources where one of multiple paths is taken based on a condition (e.g., if-then-else, match expressions)

2. **Parallel Composition (`StyParallel`)**: Represented by parallel branches that eventually join at a common event using the `Later` event source

### Event Sources

Event sources (defined in `eventGraph.ml`) map to session types as follows:

- **`Root`**: Start of a thread - begins session type checking
- **`Seq`**: Sequential progression with atomic delays (cycles, sends, receives)
- **`Branch`**: Branching point for internal choice
- **`Later`**: Synchronization point where parallel branches join

## Implementation

### Key Functions

1. **`extract_atomic_actions`**: Extracts message send/receive actions from an event
   - Handles both immediate and sustained actions
   - Returns a list of `Lang.atomic_action`

2. **`event_satisfies_atomic`**: Checks if an event's actions satisfy a required atomic action

3. **`session_judgement`**: Advances session type based on event actions
   - Takes current session type and event
   - Returns updated session type (or None if completed)
   - Handles all session type constructs except external choice

4. **`check_session`**: Main entry point for session type checking
   - Performs BFS traversal of event graph
   - Assigns session types to events
   - Validates protocol conformance

### Algorithm

The session type checker uses a BFS traversal:

```ocaml
1. Start at root event with initial session type
2. For each event:
   a. Assign current session type to event
   b. Compute next session type based on event's actions
   c. Handle branching:
      - For Branch events: propagate to all branches
      - For normal events: propagate to successors
3. Verify all events are reachable
```

### Branching Semantics

- **Internal Choice (`StyChoice`)**: When encountering a Branch event, the checker tries both alternatives. If either branch can proceed, the session continues with that branch.

- **Parallel (`StyParallel`)**: Both sub-sessions must be satisfied (possibly at different events). The checker tracks progress of both branches independently until they join.

## Usage

Session type checking is automatically invoked during graph building if a process has an interface protocol specified:

```ocaml
(* In graphBuilder.ml *)
match proc_interface_protocol with
| Some _ -> LifetimeCheck.check_session config graph
| None -> (* Skip session type checks *)
```

## Limitations

1. **External Choice Not Supported**: `StyChoiceDual` is not yet implemented. This construct would require new language syntax to specify which party makes the choice.

2. **Simplified Delay Handling**: Currently treats delays simply by decrementing cycle counts. More sophisticated timing analysis may be needed.

3. **No Error Recovery**: Failed session type checks raise exceptions rather than providing detailed diagnostic information.

## Future Work

1. **External Choice**: Add language constructs and implementation for external choice
   - Requires syntax for specifying offering behaviors
   - Needs negotiation protocol between parties

2. **Better Error Messages**: Provide detailed information about:
   - Where session type was violated
   - Expected vs. actual actions
   - Suggested fixes

3. **Session Type Inference**: Automatically infer session types from event graphs

4. **Multi-party Session Types**: Extend to protocols involving more than two parties

## Example

```anvil
// Session type for a simple request-response protocol
session SimpleProtocol(req: Chan<Request>, resp: Chan<Response>) =
  req.send ; resp.recv

// The event graph checker will verify:
// 1. Request is sent before response is received
// 2. No other messages interfere with the protocol
// 3. Timing constraints are satisfied
```

## References

- Session types: Honda et al. "An Interaction-based Language and its Typing System"
- Event graphs: See `eventGraph.ml` and related documentation
- Implementation: `lifetimeCheck.ml` lines 763-910
