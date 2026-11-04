# Kelvin–Voigt homogenization and approximation

Lean formalization of *Operator Learning of Microstructure-Dependent
Internal-Variable Models for Inelastic Homogenization: Approximation and
Complexity*, by Lianghao Cao, George Stepaniants and Andrew M. Stuart.
The final paper will be added to `paper/` at the repository root.

[MainResults.lean](KVApproximation/MainResults.lean) collects the five main
statements in paper order, with all parameters and hypotheses on each
declaration. Its short proofs invoke the original results, whose declarations
and detailed proofs remain in the subject modules. Open this file in Cursor or
VS Code to check all five main results in one place.

The [reader's guide](READER_GUIDE.md) links the definitions used in these
statements and the records that verify their proofs.

All **331 Comparator configurations and 702 selected declarations** passed
the sandboxed Linux comparison and all six bundled kernels. The build,
transitive axiom audit and subject consumer checks also passed.
[STATUS.md](STATUS.md) summarizes the coverage and verification results.
[formalization.yaml](formalization.yaml) maps the paper to Lean declarations;
[PLAN.md](PLAN.md) describes the scope and proof structure.

## Build

Lean, Mathlib and LeanCert are pinned to **v4.35.0**. With Elan installed,
run from this directory:

```sh
lake build KVApproximation Challenges TauCeti ForTauCeti NeuralNetworkProofs
```

`KVApproximation` contains the proof library. `Challenges` contains separate
Comparator statements with designated theorem placeholders. Comparator
configurations are in `Comparator/`. Sandboxed validation runs on Linux.
The [coverage report](Verification/results/vm/combined/coverage.json) combines
251 GitHub Actions results with 80 local Linux results.

## Verification

Run the build and transitive axiom audit with Python 3:

```sh
python3 Verification/verify.py local
```

The audit covers every Comparator selection and checks that the reported
axioms are limited to `propext`, `Classical.choice` and `Quot.sound`.
It includes the five declarations in `MainResults.lean` and checks that their
fully quantified types agree exactly with the original subject declarations.
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
selections, and six kernel acceptance records are present.

The dependency/build cache uses the key `comparator-linux-4.35.0-v2`.
Update this release-labelled key when changing the pinned toolchain or dependency
set. Lean/Lake checks source freshness when building restored artifacts.
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

For the prepared Lima VM on macOS, start the VM and run:

```sh
bash Verification/vm.sh
```

The script copies the proof sources and preserved CI evidence, installs the
pinned Linux toolchain and bubblewrap, rebuilds every library and audits its
axioms. It then runs only missing or failed configurations, with the default
sandbox and all six kernels. The compactness and Green pilot configurations
run first. Each local result is retained immediately inside the VM, so an
interrupted run can resume without repeating successful checks. After the serial pilot, the
runner allows at most two concurrent checks when its measured memory use fits
the VM; otherwise it continues serially.

Terminal output is saved to `Verification/results/vm/runner.log`; build, audit,
local and combined result files are copied there when the run ends. The combined
coverage report must account for all 331 configurations and 702 selections.
Use `--prepare-only` to install dependencies without starting validation.
Saved results apply to the proof sources used in their run. After a proof edit,
rerun the affected configurations.

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
