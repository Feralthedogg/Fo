#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
go run "$ROOT/scripts/generate-stdlib-symbol-index.go"
