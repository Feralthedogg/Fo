# Syntax

This document is the practical surface-language guide for Fo as it exists in this repository today.

## File Shape

Every source file starts with a package clause:

```fo
package main
```

Imports use Go-like string paths:

```fo
import "fmt"
import "github.com/Feralthedogg/Fo/stdlib/fo"
```

## Declarations

Functions:

```fo
func Add(x int, y int) int {
    return x + y
}
```

Methods:

```fo
func (p Point) Translate(dx int, dy int) Point {
    return Point{X: p.X + dx, Y: p.Y + dy}
}
```

Structs:

```fo
type Point struct {
    X int
    Y int
}
```

Interfaces:

```fo
type Stringer interface {
    String() string
}
```

Enums:

```fo
type Shape enum {
    Circle(int)
    Rect(int, int)
    Dot
}
```

Generics:

```fo
func Identity[T any](x T) T {
    return x
}
```

Function literals:

```fo
func Apply(x int, f func(int) int) int {
    return f(x)
}
```

## Expressions

Immutable local binding uses `:=`:

```fo
x := 1
y := x + 2
```

There is no mutable `var` surface.

Conditionals:

```fo
if x < 0 {
    return -x
}
```

Switch:

```fo
switch {
case x < 0:
    return -1
default:
    return 0
}
```

Pattern matching:

```fo
match s {
case Circle(r):
    return r * r * 3
case Dot:
    return 0
}
```

Pipeline:

```fo
return x |> Double |> Inc |> Negate
```

Slice pipelines that end in `Map`/`Filter`/`Fold`-style collection combinators are candidates for single-loop lowering in the Go backend.

Struct literal:

```fo
Point{X: 1, Y: 2}
```

Copy-update:

```fo
return user{Age: user.Age + 1}
```

Slices and indexing are available in the Go-like form.

## Runtime-Oriented Types

The repository uses `Cmd`, `Task`, `Option`, `Result`, and collection helpers through [`stdlib/fo`](../stdlib/fo).

That is the preferred high-level surface for effects and concurrency.

## Restricted Surface

The parser/checker intentionally rejects several Go constructs from ordinary Fo source:

- `var`
- `for`
- `go`
- `defer`
- `select`
- `goto`
- `fallthrough`
- `panic`
- `recover`

`chan` is not part of the intended user-facing surface; use `Task`-level APIs instead.

## Examples

Working examples in this repository:

- [hello.fo](../examples/hello.fo)
- [struct.fo](../examples/struct.fo)
- [pipeline.fo](../examples/pipeline.fo)
- [pipeline_bind.fo](../examples/pipeline_bind.fo)
- [pipeline_fusion.fo](../examples/pipeline_fusion.fo)
- [copyupdate.fo](../examples/copyupdate.fo)
- [enum.fo](../examples/enum.fo)

If syntax and implementation ever diverge, the implementation wins. This file is a practical guide, not a formal grammar.
