# Green interface repair diagnostic

The Linux Comparator run rejected `homogenized_green` because the challenge
and solution had different definitions for
`KVApproximation.Homogenization.HomogenizedGreen.instDualNormedSpace`.
`GreenDualSpace.lean` now supplies the same four dual-space structures to
both sides. It contains no selected solution theorem.

`green-affected-types.log` records matches for all four selections across
the three affected configurations. `CompareInterfaces.lean` additionally
calls the bundled `Lake.Check.compareAt` on compiled environments to compare
the Green statements and their supporting declarations. Its successful local
result is in `comparison.json` and `green-interfaces.log`.

This diagnostic ran on macOS. It does not run a sandbox, export comparison,
or independent kernel replay, and it is excluded from CI coverage. The
sandboxed Linux paranoid check remains required.
