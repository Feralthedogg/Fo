#!/usr/bin/env sh
set -eu

REPO="${FO_REPO:-Feralthedogg/Fo}"
API_URL="${FO_API_URL:-https://api.github.com/repos/$REPO}"
INSTALL_DIR="${FO_INSTALL_DIR:-$HOME/.local/bin}"
VERSION="${FO_VERSION:-}"

resolve_version() {
  if [ -n "$VERSION" ]; then
    printf '%s\n' "$VERSION"
    return
  fi
  curl -fsSL "$API_URL/releases/latest" | sed -n 's/.*"tag_name"[[:space:]]*:[[:space:]]*"\([^"]*\)".*/\1/p' | head -n 1
}

detect_os() {
  case "$(uname -s)" in
    Linux) printf '%s\n' "linux" ;;
    Darwin) printf '%s\n' "darwin" ;;
    *)
      printf '%s\n' "unsupported host OS: $(uname -s)" >&2
      exit 1
      ;;
  esac
}

detect_arch() {
  case "$(uname -m)" in
    x86_64|amd64) printf '%s\n' "amd64" ;;
    arm64|aarch64) printf '%s\n' "arm64" ;;
    *)
      printf '%s\n' "unsupported host architecture: $(uname -m)" >&2
      exit 1
      ;;
  esac
}

VERSION="$(resolve_version)"
OS_NAME="$(detect_os)"
ARCH_NAME="$(detect_arch)"
ASSET="fo-$VERSION-$OS_NAME-$ARCH_NAME.tar.gz"
URL="https://github.com/$REPO/releases/download/$VERSION/$ASSET"
TMPDIR="$(mktemp -d)"
ARCHIVE_PATH="$TMPDIR/$ASSET"

trap 'rm -rf "$TMPDIR"' EXIT INT TERM

mkdir -p "$INSTALL_DIR"
curl -fsSL "$URL" -o "$ARCHIVE_PATH"
tar -xzf "$ARCHIVE_PATH" -C "$TMPDIR"
cp "$TMPDIR/fo" "$INSTALL_DIR/fo"
chmod +x "$INSTALL_DIR/fo"

printf '%s\n' "Installed Fo to $INSTALL_DIR/fo"
case ":$PATH:" in
  *":$INSTALL_DIR:"*) ;;
  *)
    printf '%s\n' "$INSTALL_DIR is not on PATH. Add it to your shell profile."
    ;;
esac
