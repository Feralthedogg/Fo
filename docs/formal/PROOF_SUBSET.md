# Proof Subset

This document freezes the first proof target so that theorem statements remain stable.

## 1. Name

The proof target is called:

- `FoCore-v1`

It is the elaborated, monomorphized subset of Fo used by the first mechanized proof.

## 2. Included Source Features

`FoCore-v1` includes:

- literals
  - `Unit`
  - `Bool`
  - `Int`
  - `String`
- tuples
- structs
- enums
- local immutable bindings
- pure function calls
- unary and binary operators
  - arithmetic, comparison, and boolean operators including `!`, `&&`, and `||`
- `if`
- exhaustive `match`
- copy-update
- direct recursion
- self tail recursion
- pipeline after desugaring

## 3. Excluded Source Features

The first proof target excludes:

- `extern`
- `Cmd`
- `Task`
- interface conformance as a semantic proof target
- module graph resolution
- CLI/workspace behavior
- formatter output preservation
- parser recovery behavior

Generics are included only after elaboration:

- the formal source language is monomorphized
- generic surface syntax is not the primary theorem surface for `FoCore-v1`

## 4. Included Target Features

The target calculus `GoCore-v1` includes:

- structs
- interfaces for enum encoding
- function calls
- `if`
- `switch`
- loops used for self tail recursion
- returns
- immutable local reasoning at the proof layer

## 5. Repository Mapping

The currently verified repository corpus overlapping with `FoCore-v1` is:

- full supported example corpus
  - `examples/hello.fo`
  - `examples/tailcall.fo`
  - `examples/struct.fo`
  - `examples/pipeline.fo`
  - `examples/pipeline_bind.fo`
  - `examples/pipeline_fusion.fo`
  - `examples/integration.fo`
  - `examples/copyupdate.fo`
  - `examples/enum.fo`
- stdlib proof-facing core
  - `stdlib/fo/base.fo`

The following files are verified by regression but not part of the first semantic proof target:

- `stdlib/fo/collections.fo`
- `stdlib/fo/effects.fo`

Reason:

- they involve host-facing bridge declarations and runtime-oriented APIs

## 6. First Theorem Set

The first theorem set for `FoCore-v1` is:

1. source determinism
2. type soundness
3. pattern soundness
4. copy-update correctness
5. tail-call lowering correctness
6. enum lowering correctness
7. codegen semantic preservation

## 7. Expansion Path

After `FoCore-v1`, the next proof subsets are:

- `FoCore-v2`: generic elaboration correctness
- `FoCore-v3`: bridge declarations and abstract effect descriptions
- `FoCore-v4`: selected runtime laws for `Cmd` and `Task`

This keeps the proof program incremental instead of all-or-nothing.
