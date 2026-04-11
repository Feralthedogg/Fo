# Mechanization Plan

This document records how formal proof artifacts are expected to live in the repository.

## 1. Lean Track

Lean files live under:

- [proof/lean/Fo](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo)

Planned files:

- `Syntax.lean`
- `Semantics.lean`
- `Typing.lean`
- `Codegen.lean`
- `Env.lean`
- `Pattern.lean`
- `CoreLite.lean`
- `CoreMatch.lean`
- `CoreUpdate.lean`

Purpose:

- concise theorem statements
- readable inductive definitions
- executable proof sketches

## 2. Coq Track

Coq files live under:

- [proof/coq/Fo](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo)

Planned files:

- `Syntax.v`
- `Semantics.v`
- `Typing.v`
- `Codegen.v`
- `Env.v`
- `Pattern.v`
- `CoreLite.v`
- `CoreMatch.v`
- `CoreUpdate.v`

Purpose:

- alternate mechanization path
- more traditional proof engineering style

## 3. Repository Policy

The repository now has:

- a placeholder-free Lean tree
- a placeholder-free Coq tree
- zero line-based explicit assumptions (`axiom` / `Axiom` / `Parameter`)

Some large-core theorems are still simplified compared with the eventual full
language proof target, but the repository no longer relies on explicit theorem
assumption boundaries.

## 4. Progress Markers

We will use three states:

- `specified`
  theorem statement exists
- `sketched`
  important lemmas and proof structure exist
- `proved`
  proof is complete in the theorem prover

Current repository state:

- specified: yes
- sketched: yes, across the large-core track
- proved: yes, across concrete slices and large-core boundaries
- assumed: no

## 5. Current Proof Graph

The mechanized `Codegen` layer now has an explicit staged graph:

- phase artifact extraction
- artifact reflection
- artifact well-formedness
- artifact semantic soundness
- certificate packaging
- codegen witness construction
- compiled observation lemmas
- optimization-specific observation chains
- semantic observation bundles for branch selection, enum encoding, path-local update, tail recurrence, and single-stage pipelines
- separate lowered-target models for `copy-update`, `pipeline`, and `tailcall`
- canonical upper-surface theorem aliases that point at those target-aware chains
- compatibility-wrapper theorem aliases for older root/path/single/recur entrypoints

This does not yet mean full compiler correctness is complete.

- the graph shape exists in both Lean and Coq
- the observation predicates are still intentionally lightweight
- the next step is to strengthen semantics so these predicates become more discriminating

## 6. Claim Discipline

Allowed:

- “proof target defined”
- “theorem skeleton exists”
- “regression corpus matches”

Not allowed yet:

- “formally proved equivalent”
- “type soundness theorem completed”
- “codegen correctness theorem completed”

This distinction matters.

See also:

- [STATUS.md](/Users/feral/Desktop/Programming/Fo/docs/formal/STATUS.md)
