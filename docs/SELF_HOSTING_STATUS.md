# Self-Hosting Status

## Current State

The active repository root is now centered on the Fo-first self-hosted path.

- current compiler: [build/fo](/Users/feral/Desktop/Programming/Fo/build/fo)
- rebuilt Fo-written compiler: [build/fo-selfhosted](/Users/feral/Desktop/Programming/Fo/build/fo-selfhosted)
- active binary outputs live under `build/`; `bootstrap/bin` is now considered a stale legacy artifact path
- active caches live under `.fo-cache` by default and can be relocated with `FO_CACHE_ROOT`
- optional published cold-start seed artifact path: `bootstrap/seed`
- optional published Fo-side genesis seed artifact path: `bootstrap/seed-genesis`
- on-demand generated `base` Go package sourced from:
  - [base.fo](/Users/feral/Desktop/Programming/Fo/stdlib/fo/base.fo)
  - [collections.fo](/Users/feral/Desktop/Programming/Fo/stdlib/fo/collections.fo)
  - [effects.fo](/Users/feral/Desktop/Programming/Fo/stdlib/fo/effects.fo)
  - [bridge.gotmpl](/Users/feral/Desktop/Programming/Fo/stdlib/fo/bridge.gotmpl)

The repository root now carries zero handwritten `.go` files. Historical
bootstrap material has been moved under [Legacy](/Users/feral/Desktop/Programming/Fo/Legacy).

## Active Workflow

The maintained root workflow is:

1. build or rebuild the Fo-written transpiler with [build-selfhosted-cli.sh](/Users/feral/Desktop/Programming/Fo/scripts/build-selfhosted-cli.sh)
2. promote it with [promote-selfhosted-cli.sh](/Users/feral/Desktop/Programming/Fo/scripts/promote-selfhosted-cli.sh) when desired
3. verify representative self-hosted usage with [check-selfhosted-workflow.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-selfhosted-workflow.sh)
4. clear caches with [clean-cache.sh](/Users/feral/Desktop/Programming/Fo/scripts/clean-cache.sh) when you want a cold local rebuild or to relocate caches
5. freeze and verify the cold-start seed with:
   - [freeze-seed-snapshot.sh](/Users/feral/Desktop/Programming/Fo/scripts/freeze-seed-snapshot.sh)
   - [publish-seed-snapshot.sh](/Users/feral/Desktop/Programming/Fo/scripts/publish-seed-snapshot.sh) when you want to refresh the optional canonical artifact
   - [build-cold-seed-cli.sh](/Users/feral/Desktop/Programming/Fo/scripts/build-cold-seed-cli.sh), which now freezes a temp seed by default
   - [check-cold-seed-cli.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-cold-seed-cli.sh)
6. verify the Fo-side genesis seed plan with:
   - [materialize-genesis-seed.sh](/Users/feral/Desktop/Programming/Fo/scripts/materialize-genesis-seed.sh)
   - [publish-genesis-seed.sh](/Users/feral/Desktop/Programming/Fo/scripts/publish-genesis-seed.sh) when you want to refresh the optional canonical artifact
   - [check-genesis-seedplan-parity.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-genesis-seedplan-parity.sh)
   - [check-genesis-seed-materialization.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-genesis-seed-materialization.sh)
   - [check-genesis-seed-executor.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-genesis-seed-executor.sh)
   - [check-genesis-bootstrap-candidate.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-genesis-bootstrap-candidate.sh)

## Archive Boundary

The active root workflow no longer depends on the older bootstrap source trees
or the old stage ladder during normal operation.

## Cold-Start Boundary

The cold-start seed still uses Go as its host language, but the verified path no
longer depends on archived bootstrap source trees during normal rebuilds once
the seed has been frozen.

## Repo Hygiene

The repository checks:

- generated base files stay reproducible via [check-generated-base-runtime.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-generated-base-runtime.sh)
- the bootstrapless rebuild path works via [check-bootstrapless-rebuild.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-bootstrapless-rebuild.sh)
- the cold-seed path works via [check-cold-seed-cli.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-cold-seed-cli.sh)
- the genesis candidate path works via [check-genesis-bootstrap-candidate.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-genesis-bootstrap-candidate.sh)
- scripts do not directly rebuild from the archived genesis tree via [check-no-genesis-build-dependency.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-no-genesis-build-dependency.sh)
- the repository has zero handwritten `.go` files via [check-canonical-go-core.sh](/Users/feral/Desktop/Programming/Fo/scripts/check-canonical-go-core.sh)
