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
- large-core boundary files also exist for:
  - semantics
  - typing
  - codegen
- repository scripts still treat the formal track as an auxiliary verification layer, not the primary release gate

Operationally:

- `scripts/check-formal.sh` runs both formal check tracks
- `scripts/check-formal-lean.sh` runs the Lean checks
- `scripts/check-formal-coq.sh` runs the Coq checks

If more formal detail is needed later, it should be reconstructed from the proof tree itself rather than re-expanding the docs set into many parallel markdown summaries.
