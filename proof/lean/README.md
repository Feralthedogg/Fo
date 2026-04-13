# Lean Proof Track

This directory contains the Lean-side mechanized proof track for Fo.

Current status:

- syntax, semantics, typing, and codegen layers are mechanized
- concrete local proof slices are discharged in `CoreLite`, `CoreMatch`, and `CoreUpdate`
- codegen now carries artifact, certificate, target-aware, and observation layers
- the active Lean tree is placeholder-free
- the full implementation-level correctness story is still incomplete
- CLI/workspace orchestration, cache behavior, and self-hosted rebuild scripts are outside the primary Lean proof surface
- local proof checks require `lean` to be installed and available on `PATH`

The current role of the Lean track is no longer just theorem declaration. It is
an active mechanization surface with lightweight large-core predicates and
heavier concrete local slices.
