# CLI

This document describes the user-facing Fo CLI that is wired through [`cmd/fohost/main.fo`](../cmd/fohost/main.fo) and [`internal/toolchain/toolchain.fo`](../internal/toolchain/toolchain.fo).

## Commands

Current command surface:

- `fo init [module]`
- `fo new <module|name>`
- `fo mod init <module>`
- `fo mod tidy`
- `fo mod graph`
- `fo build [path...]`
- `fo check [path...]`
- `fo run [path...]`
- `fo test [path...]`
- `fo fmt [path...]`
- `fo format [path...]`
- `fo version`
- `fo help`

## Path Modes

The CLI accepts two broad target styles.

Explicit file targets:

```sh
fo check ./examples/hello.fo
fo build ./cmd/fohost/main.fo
```

Package or directory targets:

```sh
fo check ./cmd/fohost
fo build ./cmd/fohost
fo check ./...
```

`build .` means “build the Fo package rooted in the current directory”, not “build the whole module”.

If the current directory has no top-level `.fo` package, `build .` fails.

## What `build` Produces

For non-`main` targets, `build` writes generated Go output.

For `main` targets with a binary entrypoint, `build` produces a binary under `build/`.

Examples:

- `fo build ./examples/hello.fo`
  - no `main()` entrypoint in that file
  - writes generated Go only
- `fo build ./cmd/fohost`
  - package `main`
  - produces `build/cmd/fohost`

## `check`

`check` runs parse/type/codegen validation without compiling a final host binary.

Examples:

```sh
fo check ./examples/struct.fo
fo check ./stdlib/fo/base.fo ./stdlib/fo/collections.fo ./stdlib/fo/effects.fo
fo check ./...
```

Multiple explicit `.fo` arguments are supported for `check`.

The CLI cache keeps parse/check/codegen results separated by both source content and the currently running compiler binary. Rebuilding or promoting the compiler does not silently reuse stale cache entries from an older binary.

## `run`

`run` executes generated code through the host Go toolchain.

Examples:

```sh
fo run ./examples/copyupdate.fo
fo run ./cmd/fohost
```

Package `run` currently expects one package target at a time.

## `test`

`test` follows the same target conventions as `run`, but routes through `go test`.

## `fmt`

`fmt` formats generated Go for the selected Fo source target(s).

## `format`

`format` exists in the command surface, but in the current repository it is still only a planned command, not a complete formatter pipeline.

## Project Commands

`init`, `new`, and `mod` operate on Fo project metadata:

- `fo.mod`
- `fo.lock`

These commands are planning/file-generation commands, not package compilation commands.

## Useful Local Workflow

Common repository workflow:

```sh
perl scripts/build-selfhosted-cli.sh
perl scripts/promote-selfhosted-cli.sh
./build/fo-selfhosted check ./cmd/fohost
./build/fo-selfhosted build ./cmd/fohost
```

For release-grade binaries, use the GitHub release assets instead of building from a random checkout.
