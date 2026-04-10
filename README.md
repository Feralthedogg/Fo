# Fo

This repository root is the Fo-first self-hosting workspace for the Fo transpiler.

Current status:

- `build/fo` is the current self-hosted Fo transpiler.
- `build/fo-selfhosted` is the rebuilt Fo-written transpiler binary.
- `stdlib/fo/*.fo` contains the canonical Fo standard-library source snapshot.
- `scripts/check-formal.sh` runs both the Lean and Coq proof build checks.
- `scripts/build-selfhosted-cli.sh` rebuilds the Fo-written transpiler directly from `build/fo`.
- `scripts/promote-selfhosted-cli.sh` promotes that rebuilt binary back to `build/fo`.
- all active compiler binaries now live under `build/`; `bootstrap/bin` is no longer part of the maintained workflow.
- active caches live under `.fo-cache` by default and can be relocated with `FO_CACHE_ROOT`.
- `scripts/clean-cache.sh` removes the active cache root.
- `scripts/check-selfhosted-workflow.sh` verifies representative self-hosted `check` and `build` workflows.
- `.github/workflows/ci.yml` runs hygiene checks on macOS/Linux and can run full seeded self-hosted CI when the repository variable `FO_SEED_URL` is configured.
- `.github/workflows/release.yml` publishes tagged releases, builds OS-specific binaries, ships `install.sh` / `install.ps1`, and builds a Windows `.msi` that adds Fo to the user `PATH`.
- the seeded CI and release workflows expect `FO_SEED_URL`, with optional `FO_SEED_SHA256`, as repository variables.
- `scripts/freeze-seed-snapshot.sh` freezes a generated Go seed snapshot to a temp target by default.
- `scripts/publish-seed-snapshot.sh` publishes the optional canonical `bootstrap/seed` artifact.
- `scripts/build-cold-seed-cli.sh` builds a cold-start CLI from a temp seed snapshot by default, or from an explicit published snapshot if given.
- `scripts/check-cold-seed-cli.sh` verifies the cold-start seed snapshot path end-to-end.
- `scripts/check-genesis-seedplan-parity.sh` verifies that the Fo-side genesis seed plan matches the full practical frozen seed snapshot surface.
- `scripts/check-genesis-seed-materialization.sh` verifies that the Fo-side seedplan helpers agree with the actual frozen seed contents.
- `scripts/materialize-genesis-seed.sh` materializes a genesis seed directory to a temp target by default.
- `scripts/publish-genesis-seed.sh` publishes the optional canonical `bootstrap/seed-genesis` artifact.
- `scripts/check-genesis-seed-executor.sh` verifies that the materialized genesis seed matches the frozen snapshot on the full file surface.
- `scripts/check-genesis-bootstrap-candidate.sh` verifies the full genesis candidate path: Fo-native genesis smoke, seed-plan parity, and cold-seed CLI.
- `Legacy/` contains the archived stage-0 bootstrap sources, smoke inputs, and stage-ladder scripts.
- `docs/SELF_HOSTING_STATUS.md` records the current self-hosting gap precisely.
- `docs/formal/SEMANTICS.md` defines the proof-oriented `FoCore` and `GoCore` semantics.
- `docs/formal/CORRECTNESS.md` records the codegen and soundness obligations required for a true mathematical equivalence claim.
- `docs/formal/PROOF_SUBSET.md` freezes the first proof target subset.
- `docs/formal/MECHANIZATION.md` records the mechanization plan and claim discipline.
- `docs/formal/STATUS.md` records which parts are proved or still sketched.
- `proof/lean/Fo/*.lean` contains the Lean formalization track.
- `proof/coq/Fo/*.v` contains the Coq formalization track.

The current CLI slice includes pure command planning for:

- `init`
- `new`
- `mod`
- `build`
- `check`
- `run`
- `test`
- `fmt`
- `format`
- `version`
- `help`

Currently verified Fo-side compiler slices:

- `internal/token`
- `internal/diagnostic`
- `internal/ast`
- `internal/lexer`
- `internal/parser`
- `internal/checker`
- `internal/codegen`
- `internal/driver`
- `cmd/fo`

Currently verified real examples through stage-1 and stage-2:

- `examples/hello.fo`
- `examples/tailcall.fo`
- `examples/struct.fo`
- `examples/pipeline.fo`
- `examples/integration.fo`
- `examples/copyupdate.fo`
- `examples/enum.fo`

These example checks now validate Fo-to-Go emission, generated-Go compilation, stage-2/stage-3 second-generation stability for the supported corpus, and stage-0/stage-1 normalized-equivalence for the supported example corpus.

Currently verified stdlib surface through stage-1 and stage-2:

- `stdlib/fo/base.fo`
- `stdlib/fo/collections.fo`
- `stdlib/fo/effects.fo`

These stdlib checks now cover `check`, `build`, generated Go compilation, stage-1/stage-2 normalized output equivalence, and stage-2/stage-3 stability.

Currently verified stage-0/stage-1 stdlib parity corpus:

- `stdlib/fo/base.fo`
- `stdlib/fo/collections.fo`
- `stdlib/fo/effects.fo`

The intended long-term pipeline is:

1. Stage 0: build `fo-bootstrap` from the Go implementation.
2. Stage 1: keep the transpiler implementation in Fo source at the repository root.
3. Stage 2: use `fo-bootstrap` to transpile the Fo implementation of Fo.
4. Stage 3: compare generated Go output and behavior with the stage-0 compiler.
5. Stage 4: replace the bootstrap compiler once stage parity is proven.

At the moment, this workspace contains verified self-hosting slices, not a completed self-hosted compiler.

For daily workflow, the repository can now also produce a published stage-3 CLI:

- `scripts/build-selfhosted-cli.sh`
- output: [build/fo-selfhosted](/Users/feral/Desktop/Programming/Fo/build/fo-selfhosted)

It can also promote the next self-rebuilt generation as the default local CLI:

- `scripts/promote-selfhosted-cli.sh`
- output: [build/fo](/Users/feral/Desktop/Programming/Fo/build/fo)

For cold-start bootstrap without consulting archived bootstrap source
tree during the build itself, the frozen seed now carries only the generated
compiler core, the canonical host entry under
[cmd/fohost](/Users/feral/Desktop/Programming/Fo/cmd/fohost), and the
generated `base` Go package materialized on demand under `stdlib/fo` from
[base.fo](/Users/feral/Desktop/Programming/Fo/stdlib/fo/base.fo),
[collections.fo](/Users/feral/Desktop/Programming/Fo/stdlib/fo/collections.fo),
[effects.fo](/Users/feral/Desktop/Programming/Fo/stdlib/fo/effects.fo), and
[bridge.gotmpl](/Users/feral/Desktop/Programming/Fo/stdlib/fo/bridge.gotmpl).
The repository root now keeps no checked-in generated `base` package `.go` files and
still has zero handwritten `.go` files:

- optional published snapshot artifact path: `bootstrap/seed`
- temp freeze: `scripts/freeze-seed-snapshot.sh`
- publish canonical snapshot: `scripts/publish-seed-snapshot.sh`
- build: `scripts/build-cold-seed-cli.sh` -> `build/fo-coldseed`
- dependency check: `scripts/check-no-genesis-build-dependency.sh`
- core check: `scripts/check-canonical-go-core.sh`

## Formal Track

The repository now includes a formal proof scaffold:

- source/target semantics documents
- explicit correctness obligations
- a fixed proof subset (`FoCore-v1`)
- concrete proof slices (`CoreLite`, `CoreMatch`, `CoreUpdate`)
- Lean formalization files
- Coq formalization files

These artifacts define the proof target precisely, and the repository now also
ships machine-check scripts for both the Lean and Coq tracks. The current proof
tree is placeholder-free and has zero line-based explicit assumptions
(`axiom` / `Axiom` / `Parameter`) under the repository scripts.
