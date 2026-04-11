# Fo

Fo is a Fo-first self-hosting transpiler workspace.

## What Is Here

- `build/fo` is the current local compiler binary.
- `build/fo-selfhosted` is the rebuilt Fo-written compiler binary.
- `cmd/`, `internal/`, and `stdlib/fo/` contain the active compiler and stdlib sources.
- `Legacy/` contains archived older bootstrap material that is no longer part of the active workflow.

## Docs

- [Syntax](docs/SYNTAX.md)
- [CLI](docs/CLI.md)
- [Formal track](docs/FORMAL.md)
- [Formal status](docs/formal/STATUS.md)

## Common Workflow

Build the self-hosted compiler:

```sh
perl scripts/build-selfhosted-cli.sh
```

Check the compiler package:

```sh
./build/fo-selfhosted check ./cmd/fohost
```

Build the compiler package:

```sh
./build/fo-selfhosted build ./cmd/fohost
```

Clean caches and transient outputs:

```sh
make clean
```

## Repository Notes

- Active caches live under `.fo-cache` by default and can be relocated with `FO_CACHE_ROOT`.
- Active release and CI workflows live under `.github/workflows/`.
- Release builds publish platform binaries, installer scripts, checksums, source tarballs, and a Windows `.msi`.
- The repository keeps active checked-in generated Go out of the main source tree; runtime Go is materialized on demand during build workflows.

## Verification

Useful local checks:

- `perl scripts/check-selfhosted-workflow.sh`
- `perl scripts/check-bootstrapless-rebuild.sh`
- `perl scripts/check-cold-seed-cli.sh`
- `perl scripts/check-genesis-bootstrap-candidate.sh`
- `perl scripts/check-canonical-go-core.sh`
- `perl scripts/check-formal.sh`
