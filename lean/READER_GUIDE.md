# Reader's guide

The manual mathematical check is that the Lean statements and the definitions
they use express the intended mathematics. The recorded kernel checks establish
that those formal statements follow from the permitted axioms.

## Statements and definitions

Start with the challenge statement for each result under review:

| Result | Statement | Principal definitions |
| --- | --- | --- |
| Theorem 3.1 | [Homogenization](Comparator/Challenges/Homogenization.lean) | [Weak PDEs and initial conditions](KVApproximation/Homogenization/WeakProblem.lean), [cell model](KVApproximation/Homogenization/CellOperators.lean) |
| Proposition 3.3 | [Spectral representation](Comparator/Challenges/SpectralRepresentation.lean) | [Tensor measure](KVApproximation/Spectral/TensorMeasure.lean), [bounds](KVApproximation/Spectral/Bounds.lean), [cell model](KVApproximation/Homogenization/CellOperators.lean) |
| Theorems 4.4–4.5 | [Approximation and dimension](Comparator/Challenges/UniversalApproximation.lean) | [Uniform approximation and dimension](KVApproximation/KelvinVoigt/ApproximationProblem.lean), [A1/A2](KVApproximation/NeuralOperators/Classes.lean) |
| Proposition 4.7 | [Spectral-edge discontinuity](Comparator/Challenges/SpectralEdge.lean) | [Material spectral edge](KVApproximation/KelvinVoigt/SpectralEdge.lean) |

For the appendix results and other paper claims, use `alignment.statements` in
[formalization.yaml](formalization.yaml) to locate their declarations and
challenge files. Whole-paper correspondence includes each of those claims;
some are split across several declarations.

The statement review covers:

- All hypotheses and quantifiers, including section-level `variable` and
  `include` declarations, implicit parameters and type-class assumptions.
- The definitions that give the statement its meaning, followed through their
  dependencies to familiar mathematical notions. This includes structure
  fields, notation, coercions and instances defining norms or topologies.
- Agreement with the paper's assumptions, conclusions, constants, dimensions,
  time domains and convergence notions, including the
  [mathematical qualifications](PLAN.md#mathematical-qualifications).

For example, reviewing `UniformlyApproximates` includes its material and strain
classes, `CellFamily`, `IsResponseSolution` and stress-error norm. Theorems
4.4–4.5 assume A1/A2; claims that a particular architecture satisfies A1/A2 have
their own entries in the correspondence record.

The numbering refers to the manuscript used for the recorded verification.
The final paper will be added to `paper/`; its correspondence with these
statements must be checked when it is added.

## Proof verification

Comparator matches each selected solution theorem to its challenge statement
and checks the exported proofs. The `sorry` bodies in the separate challenge
files designate statements to prove. Accepted solution proofs may depend only
on `propext`, `Quot.sound` and `Classical.choice`.

The existing verification evidence is:

- [Combined coverage](Verification/results/vm/combined/coverage.json):
  `passed: true`, 331/331 configurations and 702 selected declarations, with
  every configuration accepted by all six kernels.
- [Transitive axiom audit](Verification/results/vm/axioms.json):
  `passed: true`, covering every selected declaration and reporting only the
  three axioms above.

Theorem proof bodies can be skipped during this review: the kernels check the
proof terms and their dependencies. The mathematical review concerns the meaning
and coverage of the statements. This relies on Lean's logic and the verification toolchain, as
described in the [Lean reference](https://lean-lang.org/doc/reference/latest/ValidatingProofs/).

Saved results apply to the sources used in their run. Changes to statements,
definitions or proofs require the affected checks to be rerun using the
[verification commands](README.md#verification).
