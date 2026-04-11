# Formal Track

This repository keeps the formal side intentionally small at the docs layer.

The machine-checked sources live in:

- [`proof/lean/Fo`](../proof/lean/Fo)
- [`proof/coq/Fo`](../proof/coq/Fo)

The current proof target is the elaborated core path:

- `FoCore`
- `GoCore`

Scope:

- source/target semantics are defined in the proof files
- the first mechanized target is the pure monomorphized subset
- runtime bridge behavior, workspace orchestration, and host I/O are not the primary proof surface

Current repository claim discipline:

- allowed:
  - proof target defined
  - mechanized files present
  - concrete proof slices discharged
  - regression corpus matches
- not claimed:
  - full compiler equivalence theorem completed
  - full surface-language soundness theorem completed
  - complete codegen preservation theorem for the whole language

Current practical status:

- concrete proof slices exist for:
  - core literals / `if`
  - pattern selection subset
  - immutable copy-update subset
- active large-core theorem surfaces now exist for:
  - tailcall lowering
  - match lowering
  - copy-update lowering
  - enum lowering
  - pipeline fusion
- those lowering surfaces are now split into explicit phase artifacts/invariants plus phase-chain preservation lemmas
- large-core boundary files also exist for:
  - semantics
  - typing
  - codegen
- codegen files now also include a direct source-to-target interpretation/refinement layer for compiled expressions
- semantics files now also expose explicit helper layers for field/path update, enum tag/payload observation, branch selection, pipeline staging, and tail outcomes
- typing/codegen files also include helper-facing bridge lemmas for those semantic layers and code-shape emission lemmas for compiled forms
- codegen artifacts now also carry reflection/correspondence predicates that relate extracted plans/trees/layouts/shapes back to source expressions or programs
- codegen now also exposes separate lowered-target models and canonical upper-surface theorem names for `copy-update`, `pipeline`, and `tailcall`
- copy-update observation now carries structured `path -> head -> prefix -> child -> child-chain -> grandchild -> grandchild-chain` projections
- pipeline observation now carries stage-result and stage-trace structure instead of only final equality
- tailcall observation now carries both recur behavior and explicit call-shape witnesses
- older root/path/single/recur observation theorem names still exist, but they now serve as compatibility wrappers over the target-aware surface
- the active Lean/Coq trees are placeholder-free and no longer rely on explicit theorem-assumption boundaries
- those optimization theorems are still lighter than full implementation-complete semantic preservation
- repository scripts still treat the formal track as an auxiliary verification layer, not the primary release gate

Operationally:

- `scripts/check-formal.sh` runs both formal check tracks
- `scripts/check-formal-lean.sh` runs the Lean checks
- `scripts/check-formal-coq.sh` runs the Coq checks

If more formal detail is needed later, it should be reconstructed from the proof tree itself rather than re-expanding the docs set into many parallel markdown summaries.
