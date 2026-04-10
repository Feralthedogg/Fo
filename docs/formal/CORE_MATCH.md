# CoreMatch Proof Slice

`CoreMatch` is the next concrete proof slice after `CoreLite`.

It adds only what is needed to reason about pattern selection.

## Included

- enum values
- struct values
- wildcard and binder patterns
- tuple patterns
- enum constructor patterns
- struct field patterns
- exhaustive `match`

## Primary Theorems

1. pattern matching determinism
2. branch selection uniqueness
3. binding soundness
4. match progress for exhaustive cases

## Current Status

Currently discharged in the wildcard/binder subset:

- branch uniqueness
- binding soundness
- wildcard progress
- binder progress
- wildcard/binder substitution shape lemmas

Currently discharged for tuple / constructor / struct exact-shape cases:

- exact-match introduction lemmas
- uniqueness preservation from explicit substitution-uniqueness premises
- exact-shape progress lemmas

Still not completed:

- recursive subpattern composition
- constructor-argument decomposition
- struct-field decomposition
- exhaustive-branch progress for the full pattern language

## Repository Mapping

- Lean: [CoreMatch.lean](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo/CoreMatch.lean)
- Coq: [CoreMatch.v](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo/CoreMatch.v)
