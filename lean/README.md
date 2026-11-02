# Kelvin–Voigt homogenization and approximation

Lean formalization of *Operator Learning of Microstructure-Dependent
Internal-Variable Models for Inelastic Homogenization: Approximation and
Complexity*, by Lianghao Cao, George Stepaniants and Andrew M. Stuart.
The source paper is in [`paper/`](../paper/).

The paper proofs compile and pass the transitive axiom audit. Sandboxed
Comparator validation is still outstanding. [STATUS.md](STATUS.md) records
the source reviews and actual validation outcomes.
[formalization.yaml](formalization.yaml) maps the paper to Lean declarations;
[PLAN.md](PLAN.md) specifies the full scope and completion criteria.

## Build

Lean, Mathlib and LeanCert are pinned to **v4.35.0**. With Elan installed,
run from this directory:

```sh
lake update
lake build KVApproximation Challenges TauCeti ForTauCeti NeuralNetworkProofs
```

`KVApproximation` contains the proof library. `Challenges` contains separate
Comparator statements with designated theorem placeholders. Comparator
configurations are in `Comparator/`; authoritative sandboxed validation
requires Linux. The preserved CI results cover 251 of 331 configurations;
the remaining checks are being recovered in the local Linux VM.

## Verification

Run the build and transitive axiom audit with Python 3:

```sh
python3 Verification/verify.py local
```

The audit covers every Comparator selection and checks that the reported
axioms are limited to `propext`, `Classical.choice` and `Quot.sound`.
Commands, logs and results are saved in `Verification/results/`.

On Linux with bubblewrap, run the pinned toolchain's built-in Comparator
with all paranoid checkers:

```sh
python3 Verification/verify.py comparator
```

The `build` and `axioms` stages can also be run separately.

### GitHub Actions

The [Sandboxed Comparator workflow](../.github/workflows/comparator.yml) runs on
Ubuntu 22.04 with the pinned Linux toolchain and bubblewrap. It builds all
libraries, audits their axioms, and checks seven pilot configurations before
running the complete suite in 16 disjoint shards, with at most eight jobs at
once. Every configuration uses the default sandbox and `--paranoid`.

Use **Actions → Sandboxed Comparator → Run workflow** to start a full run or
select `pilot` to measure setup and representative checks. Relevant source and
runner changes pushed to `main` also start a full run. The workflow retains logs
and result records for 14 days and verifies that all configurations, theorem
selections, and six kernel acceptance records are present. A successful pilot
alone is not complete validation.

The dependency/build cache uses the explicit key `comparator-linux-4.35.0-v2`.
Update this release-labelled key when changing the pinned toolchain or dependency
set. Lean/Lake still checks source freshness when building restored artifacts.
The workflow frees unused preinstalled SDKs on its disposable runners and
requires the shared build cache to exist before starting the shards.

On a prepared Linux system, the same shard selection is available locally:

```sh
python3 Verification/verify.py comparator --shard-index 0 --shard-count 16 --keep-going
```

Each invocation refreshes the Comparator results in its own working copy. Collect
the shard result directories and check complete coverage with:

```sh
python3 Verification/collect_comparator.py path/to/collected-shard-results
```

For the prepared Lima VM on macOS, start the VM and run this from a normal
Terminal:

```sh
bash Verification/vm.sh
```

The script copies the proof sources and preserved CI evidence, installs the
pinned Linux toolchain and bubblewrap, rebuilds every library and audits its
axioms. It then runs only missing or failed configurations, with the default
sandbox and all six kernels. The three repaired pilot configurations run first.
Each local result is retained immediately inside the VM, so an interrupted run
can resume without repeating successful checks. After the serial pilot, the
runner allows at most two concurrent checks when its measured memory use fits
the VM; otherwise it continues serially.

Terminal output is saved to `Verification/results/vm/runner.log`; build, audit,
local and combined result files are copied there when the run ends. The combined
coverage report must account for all 331 configurations and 702 selections.
Use `--prepare-only` to install dependencies without starting validation.
Resume saved evidence only with unchanged proof sources; after a proof edit,
discard and rerun every affected configuration's earlier result.

Check subject reuse after building:

```sh
python3 Verification/consumers.py
```

Each consumer contains only that subject's recursively required local
sources and licenses. It imports the corresponding production artifacts
through an isolated library path. This checks dependency closure; the full
build above compiles the dependencies themselves.

## Modules

The library separates analysis, tensors, operator theory, spectral theory,
homogenization, approximation, dynamics, neural operators and exact examples.
`KelvinVoigt` assembles the paper's main results. Import the specific module
needed by a proof, for example:

```lean
import KVApproximation.Homogenization.StaticHomogenization
import KVApproximation.Dynamics.VariationalEvolution
```

`import KVApproximation` provides the main paper results and appendix identities.
Generic homogenization has no dependency on neural approximation or examples.

New code is licensed under [Apache-2.0](LICENSE). The selected upstream
sources in `Vendor/` retain their licenses and attribution.
