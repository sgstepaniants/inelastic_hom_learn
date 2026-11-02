#!/usr/bin/env bash
# Run the proof checks in the prepared Lima VM and retain their results.
set -euo pipefail

cd "$(dirname "$0")/.."
proof_root="$PWD"
mode="${1:-run}"
if [[ "$#" -gt 1 || ( "$mode" != run && "$mode" != --prepare-only ) ]]; then
  echo "Usage: bash Verification/vm.sh [--prepare-only]" >&2
  exit 2
fi

if [[ "$(uname -s)" == Darwin ]]; then
  ssh_config="$proof_root/.vm/lima/proof/ssh.config"
  if [[ ! -f "$ssh_config" ]]; then
    echo "Start the prepared Lima proof VM before running this script." >&2
    exit 1
  fi
  mkdir -p Verification/results/vm
  ssh -F "$ssh_config" lima-proof '
    set -eu
    mkdir -p "$HOME/lean/kv_approximation"
    cd "$HOME/lean/kv_approximation"
    mkdir -p .work
    flock -n .work/vm.lock true
    flock -n .work/local-comparator.lock true
    # Refresh the managed source copy, preserving dependency and toolchain caches.
    rm -rf KVApproximation Vendor Comparator
    mkdir -p Verification/results
    rm -rf Verification/results/ci
  '
  COPYFILE_DISABLE=1 tar --no-xattrs -cf - \
    lakefile.toml lake-manifest.json lean-toolchain .gitignore LICENSE \
    README.md PLAN.md STATUS.md formalization.yaml \
    KVApproximation.lean KVApproximation Vendor Comparator \
    Verification/verify.py Verification/consumers.py Verification/Axioms.lean Verification/vm.sh \
    Verification/collect_comparator.py Verification/resume_comparator.py Verification/test_ci.py \
    Verification/cache_dependencies.py Verification/results/ci |
    ssh -F "$ssh_config" lima-proof \
      'tar -xf - -C "$HOME/lean/kv_approximation"'

  collect_results() {
    ssh -F "$ssh_config" lima-proof \
      'cd "$HOME/lean/kv_approximation" && tar --exclude=Verification/results/ci -cf - Verification/results' |
      tar -xf - --strip-components=2 -C "$proof_root/Verification/results/vm"
  }
  trap collect_results EXIT
  remote_command='cd "$HOME/lean/kv_approximation" && bash Verification/vm.sh'
  if [[ "$mode" == --prepare-only ]]; then
    remote_command+=' --prepare-only'
  fi
  ssh -F "$ssh_config" lima-proof "$remote_command" \
    2>&1 | tee Verification/results/vm/runner.log
  exit
fi

if [[ "$(uname -s)" != Linux || "$(uname -m)" != aarch64 ]]; then
  echo "This VM setup requires aarch64 Linux." >&2
  exit 1
fi

mkdir -p Verification/results .vm/toolchains .cache/mathlib .work/tmp
exec 9>.work/vm.lock
flock -n 9 || { echo "A VM validation is already running." >&2; exit 1; }
export TMPDIR="$proof_root/.work/tmp"
export MATHLIB_CACHE_DIR="$proof_root/.cache/mathlib"
export MATHLIB_NO_CACHE_ON_UPDATE=1
unset LEAN_PATH LEAN_SYSROOT LAKE_HOME LAKE_OVERRIDE_LEAN LEAN COMPARATOR_BWRAP

sudo -n apt-get update
sudo -n apt-get install -y bubblewrap ca-certificates curl git zstd build-essential python3

lean_release="$(sed -n 's|^leanprover/lean4:v||p' lean-toolchain)"
if [[ ! "$lean_release" =~ ^[0-9]+\.[0-9]+\.[0-9]+$ ]]; then
  echo "Expected a stable Lean release in lean-toolchain." >&2
  exit 1
fi
toolchain_dir="$proof_root/.vm/toolchains/lean-$lean_release-linux_aarch64"
if [[ ! -x "$toolchain_dir/bin/lake" ]]; then
  archive="$proof_root/.vm/toolchains/lean-linux.tar.zst"
  curl --proto '=https' --tlsv1.2 --fail --location --retry 3 \
    "https://github.com/leanprover/lean4/releases/download/v$lean_release/lean-$lean_release-linux_aarch64.tar.zst" \
    --output "$archive"
  tar --zstd -xf "$archive" -C "$proof_root/.vm/toolchains"
  rm "$archive"
fi
export PATH="$toolchain_dir/bin:$PATH"
lean --version
lake --version
bwrap --version
for checker in leanexport leanchecker leanchecker-paranoid lean4lean nanoda_bin con-leche con-ron; do
  test -x "$toolchain_dir/bin/$checker"
done

# Check namespace availability without weakening the Comparator sandbox.
bwrap --unshare-all --ro-bind / / --proc /proc --dev /dev \
  --die-with-parent --new-session -- /bin/true

# Populate the standard dependency cache before the network-isolated builds.
# The committed Lake manifest, rather than an update, selects dependencies.
lake env true
python3 Verification/cache_dependencies.py
# Downloaded cache archives are no longer needed after successful extraction.
rm -rf .cache/mathlib
if [[ "$mode" == --prepare-only ]]; then
  exit
fi
python3 Verification/test_ci.py
python3 Verification/verify.py local
python3 Verification/resume_comparator.py
