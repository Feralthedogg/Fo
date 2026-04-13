# Formal Status

Current release line: `v1.1.0`

Mechanized today:

- target-aware codegen certificate chains for tailcall, pipeline, and copy-update
- structured pipeline single-stage and multi-stage observation predicates
- structured copy-update path/head/prefix ladders with child, child-chain, grandchild, and grandchild-chain projections
- constructive nested binder-path witness plumbing in Lean and Coq
- placeholder-free Lean and Coq theorem trees on the active formal path

Operational evidence surface today:

- self-hosted rebuild and promoted-seed workflows exist in the repository scripts
- bootstrapless and genesis seed workflows are tracked as executable repository checks
- these workflows are important evidence for compiler behavior, but they are not formal proof obligations by themselves

Not claimed yet:

- full type soundness
- full codegen correctness
- full semantic equivalence for every lowered target constructor

Runner prerequisites:

- `scripts/check-formal.sh` requires the local prover binaries such as `lean` and `coqc`

This file is a status checkpoint, not a proof claim.
