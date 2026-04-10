# Formal Status

This document records the current proof status more precisely than the high-level
mechanization plan.

## Status Labels

- `proved`
  The theorem body is present in the repository and does not rely on a local
  placeholder such as `sorry`, `Admitted`, `axiom`, `Axiom`, or `Parameter`.
- `sketched`
  The theorem statement and surrounding proof structure exist, but the theorem
  body still uses a placeholder.

## Important Caveat

This repository now ships runnable Lean and Coq check scripts and they have been
used in the current development environment.

That means:

- file-level proof artifacts exist
- many local theorems have concrete proof terms
- the current proof tree is mechanically checked by the repository scripts

The current proof tree is placeholder-free and assumption-free under the
repository's line-based `axiom` / `Axiom` / `Parameter` accounting.

## Current Slice Status

### `CoreLite`

Files:

- [CoreLite.lean](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo/CoreLite.lean)
- [CoreLite.v](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo/CoreLite.v)

Current state:

- `proved`:
  - lookup lemmas
  - lookup determinism lemmas
  - canonical forms for `bool`, `int`, `unit`, `string`
  - literal progress lemmas
  - tuple constructor progress helpers
  - `if` progress helpers
- `proved` in Lean:
  - canonical forms for `bool`, `int`, `unit`, `string`
- `proved` in Coq:
  - `lite_eval_deterministic`
  - `progress_lite`
- `sketched`:
  - larger theorem packaging around the concrete helpers

### `CoreMatch`

Files:

- [CoreMatch.lean](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo/CoreMatch.lean)
- [CoreMatch.v](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo/CoreMatch.v)

Current state:

- `proved`:
  - branch uniqueness for wildcard/binder subset
  - binding soundness for binder
  - wildcard/binder progress
  - wildcard/binder substitution shape lemmas
- `proved`:
  - exact-shape tuple introduction/progress lemmas
  - exact-shape constructor introduction/progress lemmas
  - exact-shape struct introduction/progress lemmas
  - uniqueness recovery from exact-shape tuple/ctor/struct proofs
- `sketched`:
  - recursive tuple pattern proofs
  - recursive constructor pattern proofs
  - recursive struct pattern proofs
  - exhaustive-branch progress for the wider pattern language

### `CoreUpdate`

Files:

- [CoreUpdate.lean](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo/CoreUpdate.lean)
- [CoreUpdate.v](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo/CoreUpdate.v)

Current state:

- `proved`:
  - lookup at updated path
  - untouched-field preservation for present fields
  - untouched-field preservation for missing fields
  - update determinism
  - overwrite shadowing
  - same-value idempotence
  - root-path lookup/update lemmas
  - one-segment nested path correctness
  - two-segment nested path correctness
- `sketched`:
  - arbitrary-length path correctness
  - nested reconstruction correctness
  - lowering preservation for general copy-update

### `FoCore-v1` Main Track

Files:

- [Semantics.lean](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo/Semantics.lean)
- [Semantics.v](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo/Semantics.v)
- [Typing.lean](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo/Typing.lean)
- [Typing.v](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo/Typing.v)
- [Codegen.lean](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo/Codegen.lean)
- [Codegen.v](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo/Codegen.v)

Current state:

- `proved`:
  - large-core deterministic semantics boundary
  - large-core canonical forms boundary
  - large-core weakening boundary
  - large-core progress boundary
  - large-core codegen preservation boundary
  - basic discrimination lemmas
  - environment lookup helper lemmas
  - `pattern_binds_unique`
- `sketched`:
  - preservation
  - substitution
  - match/copy-update/tailcall lowering correctness

## Placeholder Snapshot

At the time this file was written:

- Lean placeholders (`sorry`) have been eliminated from the current proof tree
- Coq placeholders (`Admitted`) have been eliminated from the current proof tree
- the concrete slices `CoreLite`, `CoreMatch`, and `CoreUpdate` contain the
  highest-density actual proofs in the repository
- line-based explicit assumption count (`axiom` / `Axiom` / `Parameter`):
  `0`
