#!/usr/bin/env bash
# Prepare a GitHub-hosted Linux runner for the pinned, sandboxed Comparator.
set -euo pipefail
cd "$(dirname "$0")/.."
proof_root="$PWD"

if [[ "$(uname -s)" != Linux || "$(uname -m)" != x86_64 ]]; then
  echo "This CI setup requires x86_64 Linux." >&2
  exit 1
fi

sudo -n apt-get update
sudo -n apt-get install -y bubblewrap ca-certificates curl git zstd build-essential python3

lean_release="$(sed -n 's|^leanprover/lean4:v||p' lean-toolchain)"
if [[ ! "$lean_release" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "Expected a stable Lean release in lean-toolchain." >&2
  exit 1
fi
toolchain_dir="$proof_root/.elan/toolchains/lean-$lean_release-linux"
mkdir -p .elan/toolchains .cache/mathlib
if [[ ! -x "$toolchain_dir/bin/lake" ]]; then
  archive="$proof_root/.elan/toolchains/lean-linux.tar.zst"
  curl --proto '=https' --tlsv1.2 --fail --location --retry 3 \
    "https://github.com/leanprover/lean4/releases/download/v$lean_release/lean-$lean_release-linux.tar.zst" \
    --output "$archive"
  tar --zstd -xf "$archive" -C .elan/toolchains
  rm "$archive"
fi

export PATH="$toolchain_dir/bin:$PATH"
export MATHLIB_CACHE_DIR="$proof_root/.cache/mathlib"
unset LEAN_PATH LEAN_SYSROOT LAKE_HOME LAKE_OVERRIDE_LEAN LEAN COMPARATOR_BWRAP
lean --version
lake --version
bwrap --version
for checker in leanexport leanchecker leanchecker-paranoid lean4lean nanoda_bin con-leche con-ron; do
  test -x "$toolchain_dir/bin/$checker"
done

# Fail if isolation is unavailable; never fall back to an unsandboxed run.
bwrap --unshare-all --ro-bind / / --proc /proc --dev /dev \
  --die-with-parent --new-session -- /bin/true

# Populate dependencies from the committed Lake manifest before isolated builds.
lake exe cache get
printf '%s\n' "$toolchain_dir/bin" >> "$GITHUB_PATH"
printf 'MATHLIB_CACHE_DIR=%s\n' "$MATHLIB_CACHE_DIR" >> "$GITHUB_ENV"
