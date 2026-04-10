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

## 3. Scope of the First Full Proof

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

## 4. Known Deferred Proof Obligations

The following are explicitly deferred beyond the first full proof:

- full generic elaboration correctness over the unrestricted language
- module/import resolution correctness
- host bridge correctness for `extern`
- runtime semantics for `Cmd` and `Task`
- full parser correctness
- full formatter correctness

## 5. What Counts as “Mathematically Proven”

We should only claim mathematical equivalence after all of the following exist:

1. a precise source semantics
2. a precise target semantics
3. a mechanized preservation theorem
4. a mechanized proof that the implementation follows the specified lowering

Until then:

- regression parity is strong evidence
- but not a complete proof

This document exists so the repository can move from strong evidence to actual proof.
