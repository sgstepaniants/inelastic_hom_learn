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
requires Linux and has not yet run.

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

For the prepared Lima VM on macOS, start the VM and run this from a normal
Terminal:

```sh
bash Verification/vm.sh
```

The script copies the proof sources, installs the pinned Linux toolchain and
bubblewrap, and runs the same sandboxed Comparator command for every
configuration. It saves the Terminal output to `Verification/results/vm.log`
and copies the individual results back when the run ends. Each run refreshes
the managed VM source copy and clears old Comparator results, while retaining
dependency caches and local build/axiom evidence. The runner has passed syntax
and simulated failure-handling checks; its Linux execution remains pending.

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
