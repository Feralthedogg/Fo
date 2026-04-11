# CoreUpdate Proof Slice

`CoreUpdate` isolates immutable reconstruction.

## Included

- struct values
- field paths
- copy-update
- path-local reconstruction

## Primary Theorems

1. updated path correctness
2. untouched field preservation
3. reconstruction determinism
4. lowering preservation for copy-update

## Current Status

Currently discharged:

- updated-path correctness
- untouched-field preservation for present fields
- untouched-field preservation for missing fields
- overwrite shadowing
- same-value idempotence
- reconstruction determinism
- root-path lookup/update lemmas
- arbitrary-path lookup-after-success for successful updates
- one-segment nested update lookup correctness
- two-segment nested update lookup correctness relative to inner-field presence
- structured observation witnesses for path / head / prefix update views
- first-child projection theorems from prefix witnesses
- first-child recursive chain projection theorems
- grandchild projection theorems
- grandchild-chain projection theorems

Still not completed:

- arbitrary-length path correctness
- untouched-subtree preservation for general nested updates
- lowering preservation for fully general nested copy-update

## Repository Mapping

- Lean: [CoreUpdate.lean](/Users/feral/Desktop/Programming/Fo/proof/lean/Fo/CoreUpdate.lean)
- Coq: [CoreUpdate.v](/Users/feral/Desktop/Programming/Fo/proof/coq/Fo/CoreUpdate.v)
