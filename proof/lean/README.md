# Lean Proof Track

This directory contains the Lean-side mechanized proof track for Fo.

Current status:

- syntax, semantics, typing, and codegen layers are mechanized
- concrete local proof slices are discharged in `CoreLite`, `CoreMatch`, and `CoreUpdate`
- codegen now carries artifact, certificate, target-aware, and observation layers
- the active Lean tree is placeholder-free
- the full implementation-level correctness story is still incomplete

The current role of the Lean track is no longer just theorem declaration. It is
an active mechanization surface with lightweight large-core predicates and
heavier concrete local slices.
