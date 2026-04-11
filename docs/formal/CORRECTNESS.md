# Codegen Correctness Obligations

This document records the proof obligations required to claim mathematical equivalence between:

- the Go stage-0 compiler
- the Fo self-hosted compiler
- the abstract `FoCore -> GoCore` translation

## 1. Layers

There are three distinct correctness layers.

### 1. Surface-to-Core

The full Fo source language is elaborated into `FoCore`.

Obligations:

- parsing/building AST corresponds to surface syntax
- desugaring preserves meaning
  - pipeline
  - copy-update normalization
  - tuple/multi-return normalization
- generic elaboration / monomorphization preserves meaning for the proof subset

### 2. Core-to-Target

`FoCore` lowers to `GoCore`.

This is the central semantic preservation theorem.

Recommended proof order:

1. variable preservation
2. tuple preservation
3. unary preservation
4. binary preservation
5. struct preservation
6. constructor preservation
7. call preservation
8. `if` preservation
9. `match` preservation
10. copy-update preservation
11. tail-call lowering preservation
12. whole-program codegen preservation

### 3. Implementation-to-Spec

The actual compiler implementation must refine the abstract lowering relation.

This is how we connect:

- the historical Go stage-0 compiler
- `internal/*.fo`

to the mathematical specification.

## 2. Main Theorems

### T1. Determinism

If:

- `Γf, Δ, ρ ⊢ e ⇓ v1`
- `Γf, Δ, ρ ⊢ e ⇓ v2`

then:

- `v1 = v2`

### T2. Type Soundness

For well-typed `FoCore`:

- progress
- preservation
- canonical forms
- weakening
- substitution

Informally:

- well-typed closed programs do not get stuck

### T3. Pattern Soundness

If:

- `p` is well-typed against type `τ`
- `v : τ`

then:

- matching either fails legally or returns a substitution consistent with typing

And if a match is statically exhaustive:

- one branch is always selected for closed well-typed inputs

### T4. Copy-Update Correctness

If:

- `u` is a struct value
- `u' = copyUpdate(u, path := v)`

then:

- all non-updated fields are preserved
- the updated path contains the new value
- reconstruction is observationally immutable

### T5. Tail-Call Lowering Correctness

If a function is recognized as self tail recursive and lowered to a loop:

- source recursive semantics and lowered loop semantics are observationally equivalent

### T6. Match Lowering Correctness

If `match e { ... }` lowers to `switch/type-assert` form:

- selected branch is preserved
- bound values are preserved
- returned value is preserved

### T7. Enum Lowering Correctness

The enum encoding:

- source variant construction
- source pattern deconstruction

must be equivalent to the target constructor representation.

This applies to:

- non-generic enums
- generic enums after monomorphization

### T8. Codegen Preservation

If:

- `compile(e) = g`
- `e` is in the proof subset

then:

- evaluating `e` in `FoCore`
- and evaluating `g` in `GoCore`

produce the same result.

## 3. Current Mechanized Bridge

The repository now contains a staged mechanized bridge for the `Codegen` layer:

1. lowering artifact extraction
2. artifact reflection / well-formedness / semantic soundness
3. certificate construction
4. target-shape witness construction
5. compiled observation lemmas
6. optimization-specific observation chains

Concretely, the current optimization-specific observation chains cover:

- `match`
- copy-update
- enum lowering
- self tail-call lowering
- pipeline fusion

Current match observation coverage includes:

- direct ctor hit
- direct binder hit
- direct tuple hit
- direct struct hit
- tuple/struct direct hits linked to `CoreMatch` exact-progress slices
- tuple/struct direct hits linked to explicit substitution witnesses
- tuple/struct direct hits linked to both `Pattern` and `CoreMatch` witness layers
- tuple/struct direct hits linked to explicit `Pattern` / `CoreMatch` composition witnesses
- tuple/struct direct hits linked to arity-indexed recursive composition spines
- tuple/struct direct hits linked to per-subpattern recursive decomposition witnesses
- tuple/struct binder-wild immediate subpatterns linked to generated partial-substitution fragments
- tuple/struct binder-wild immediate subpatterns linked to explicit generated part lists
- tuple/struct binder-wild immediate subpatterns linked to pointwise generated-part decomposition witnesses
- nested tuple/struct binder-wild fragments linked to explicit generated part-list relations
- nested tuple/struct binder-wild fragments linked to leaf-binder domain correspondence
- nested tuple/struct binder-wild fragments linked to path-aware leaf-binder correspondence
- nested tuple/struct binder-wild fragments linked to path membership/length summary witnesses
- nested tuple/struct binder-wild fragments linked to path coverage witnesses
- nested tuple/struct binder-wild fragments linked to explicit path-bridge certificates
- nested path-bridge dependencies isolated behind certificate builders
- nested path summary/coverage dependencies isolated behind witness builders
- nested path consumers isolated behind single witness-bundle builders
- nested path provider acquisition isolated behind `OfWitness` / `OfGenerated` helper builders
- bridge-specific typing/codegen path theorems consume direct `OfGenerated` bridge-certificate builders
- Lean nested path-name bridge is now a fully constructive recursive theorem family with no remaining path-name axioms
- nested path witness bundles now carry direct binder-path/domain coverage, with matching typing/codegen bundle theorems
- nested path witness bundles now also carry per-binder leaf-to-generated-part witnesses, with matching typing/codegen bundle theorems
- nested path witness bundles now also carry joint `(path, part)` origin witnesses for each binder leaf
- typing/codegen now expose tuple/struct provenance bundles that project `leaf`, `partLeaf`, `origin`, and `valueOrigin` together
- typing/codegen now also expose binder-indexed `leafAt`, `partLeafAt`, `originAt`, and `valueOriginAt` projections
- Codegen path theorems consume typing-side witness bundles instead of per-path theorem families
- Coq nested tuple/struct binder-wild fragments linked to constructive recursive path-binding enumeration
- immediate binder-wild fragments linked to constructive local path-correspondence bundles
- tuple/struct direct hits linked to substitution-domain agreement between those witness layers
- skipped leading ctor mismatches
- wildcard fallback after skipped ctor mismatches
- ctor/wild coverage relations that imply branch selection
- exhaustive-style existence of a selected branch for the current ctor/wild/binder coverage fragment
- `copy-update`, `pipeline`, and `tailcall` now also have separate lowered-target models, target-aware soundness chains, and target-aware certificate observation theorems as the preferred upper proof surface
- legacy non-target pipeline multistage observation now projects directly from the target-aware theorem instead of rebuilding its own chain
- canonical upper-surface names now point at the target-aware theorems: `copyUpdate_certificate_semantic_observation`, `pipeline_certificate_semantic_observation`, `tailcall_certificate_semantic_observation`

These chains are stronger than a bare theorem skeleton because they connect:

- source-side helper semantics
- source-side semantic observation bundles
- phase invariants
- emitted target shape
- a target observation predicate

But they are still weaker than a final full semantic preservation proof.

## 4. Scope of the First Full Proof

The first fully mechanized proof target is:

- pure, closed, monomorphized `FoCore`
- no `extern`
- no `Cmd`
- no `Task`
- no interface dispatch obligations
- no host filesystem/process behavior

This is sufficient to cover:

- arithmetic/boolean examples
- struct examples
- enum examples
- pipeline after desugaring
- copy-update
- pure recursion and tail-call lowering

## 5. Known Deferred Proof Obligations

The following are explicitly deferred beyond the first full proof:

- full generic elaboration correctness over the unrestricted language
- module/import resolution correctness
- host bridge correctness for `extern`
- runtime semantics for `Cmd` and `Task`
- full parser correctness
- full formatter correctness

## 6. What Counts as “Mathematically Proven”

We should only claim mathematical equivalence after all of the following exist:

1. a precise source semantics
2. a precise target semantics
3. a mechanized preservation theorem
4. a mechanized proof that the implementation follows the specified lowering

Until then:

- regression parity is strong evidence
- but not a complete proof

This document exists so the repository can move from strong evidence to actual proof.
