# Coq Proof Track

This directory contains the Coq-side mechanized proof track for Fo.

Current status:

- syntax, semantics, typing, and codegen layers are mechanized
- concrete local proof slices are discharged in `CoreLite`, `CoreMatch`, and `CoreUpdate`
- codegen now carries artifact, certificate, target-aware, and observation layers
- the active Coq tree is placeholder-free
- the full implementation-level correctness story is still incomplete
- CLI/workspace orchestration, cache behavior, and self-hosted rebuild scripts are outside the primary Coq proof surface
- local proof checks require `coqc` to be installed and available on `PATH`

The Coq track mirrors the Lean track so the proof program is not locked to one
prover too early, while still keeping a live mechanized graph rather than a
declaration-only shell.
