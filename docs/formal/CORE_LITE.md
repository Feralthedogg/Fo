# CoreLite Proof Slice

`FoCore-v1` is still mostly a large theorem skeleton.

So the repository also carries a smaller concrete subset as the first place
where actual mechanized proofs can accumulate:

- `CoreLite`

## Included

- variables
- `unit`
- `bool`
- `int`
- `string`
- tuples
- `if`

## Excluded

- pattern matching
- enums
- structs
- calls outside the direct core fragment
- recursion
- copy-update
- lowering correctness

## Goal

`CoreLite` is the smallest useful slice where it is practical to discharge real
proof obligations.

1. lookup determinism
2. expression evaluation determinism
3. canonical forms for `bool` and `int`
4. progress for literals and `if`

The plan is to make this small layer solid first, then lift the same proof style
into the larger `FoCore-v1` track.

## Current Status

Currently discharged in at least one proof track:

- lookup lemmas
- lookup determinism
- canonical forms for `bool` and `int`
- canonical forms for `unit` and `string`
- literal progress
- tuple construction progress helpers
- `if` progress helpers

The Coq slice currently goes further than the Lean slice here, including a
concrete `lite_eval_deterministic` theorem and a full `progress_lite`.

## Repository Mapping

- Lean: [CoreLite.lean](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo/CoreLite.lean)
- Coq: [CoreLite.v](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo/CoreLite.v)
