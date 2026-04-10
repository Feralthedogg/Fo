# Fo Formal Semantics

This document defines the proof-oriented core language used for mathematical reasoning about the Fo compiler.

It does not attempt to formalize the entire repository surface directly.
Instead, the proof target is an elaborated core calculus:

- `FoCore`: a pure, monomorphized source calculus
- `GoCore`: a Go-shaped target calculus used as the semantic target of code generation

The intended workflow is:

1. Parse full Fo surface syntax.
2. Elaborate/desugar into `FoCore`.
3. Lower `FoCore` into `GoCore`.
4. Prove semantic preservation from `FoCore` to `GoCore`.

## 1. FoCore

`FoCore` is the source language for proofs.

Included:

- base values: `Unit`, `Bool`, `Int`, `String`
- tuples
- structs
- enums / algebraic variants
- variables
- pure function calls
- `if`
- exhaustive `match`
- immutable `copy-update`
- unary and binary operators
- `let`-style single-assignment bindings
- recursion

Excluded from the first proof target:

- modules/import resolution
- interfaces as proof obligations
- `extern`
- `Cmd`, `Task`
- host I/O
- formatting
- workspace orchestration
- parser error recovery

Generics are handled by elaboration:

- proof target programs are monomorphized before entering `FoCore`
- the proof obligation for generic elaboration is stated separately in `CORRECTNESS.md`

## 2. FoCore Syntax

Types:

- `τ ::= Unit | Bool | Int | String`
- `τ ::= Tuple[τ1, ..., τn]`
- `τ ::= Struct(Name)`
- `τ ::= Enum(Name)`
- `τ ::= Fn([τ1, ..., τn], τr)`

Values:

- `v ::= unit | true | false | n | s`
- `v ::= (v1, ..., vn)`
- `v ::= StructV(Name, { field_i = v_i })`
- `v ::= VariantV(EnumName, CtorName, [v1, ..., vn])`
- `v ::= Closure(f, ρ)`

Expressions:

- literals
- variables
- tuple literals
- struct literals
- enum constructor application
- field selection
- tuple projection
- unary op
- binary op
- pure call
- copy-update
- `if`
- `match`

Statements / blocks:

- `x := e`
- `return e`
- `if e { ... }`
- `match e { ... }`
- block sequencing

## 3. Dynamic Semantics

We use:

- environments `ρ : Var -> Value`
- global function environment `Γf`
- struct/enum definitions `Δ`

The main judgment forms are:

- expression evaluation: `Γf, Δ, ρ ⊢ e ⇓ v`
- statement evaluation: `Γf, Δ, ρ ⊢ s ⇓ (ρ', r)`
- block evaluation: `Γf, Δ, ρ ⊢ block ⇓ r`

where `r` is either:

- `Continue ρ`
- `Return v`

Key semantic properties intended for proof:

- determinism of evaluation
- absence of mutation in source states
- match branch selection is unique for exhaustive patterns
- copy-update reconstructs a fresh value and preserves untouched fields

## 4. Match Semantics

Pattern matching is defined by a matching judgment:

- `Δ ⊢ p ▷ v ⇓ θ`

meaning:

- pattern `p` matches value `v`
- producing binding substitution `θ`

Important invariants:

- wildcard produces empty substitution
- variable pattern produces a singleton substitution
- tuple/struct/enum patterns recurse structurally
- exhaustive match guarantees one selected branch for well-typed closed programs

## 5. Tail Recursion

Source semantics remains recursive.

For code generation, tail-call lowering is modeled as a semantics-preserving transformation:

- `tailLower : FoCoreFn -> FoCoreFn`

Correctness target:

- if `tailLower f = f'`
- then `f` and `f'` are observationally equivalent

This allows proof of the loop-lowered target while keeping the source semantics simple.

## 6. GoCore

`GoCore` is not full Go.
It is the proof target for generated code.

Included:

- immutable local bindings
- structured `if`
- structured `switch`
- first-order structs
- interface + constructor encoding for enums
- loops used only for validated tail-call lowering
- function calls
- returns

Excluded:

- concurrency primitives
- goroutines
- channels
- reflection
- arbitrary heap aliasing
- package init side effects

## 7. Observational Equivalence

Two closed programs are observationally equivalent when:

- both terminate with the same value, or
- both fail in the same defined way

For the current proof target we only model panic-free pure execution.

So the working equivalence notion is:

- same closed input environment
- same returned value
- no undefined behavior

## 8. Proof Strategy

The proof plan is:

1. prove `FoCore` determinism
2. prove `FoCore` type soundness
3. define elaboration from full Fo surface to `FoCore`
4. define lowering from `FoCore` to `GoCore`
5. prove semantic preservation of lowering
6. connect the implemented compiler to the abstract lowering relation

This document is the mathematical source of truth for those proofs.
