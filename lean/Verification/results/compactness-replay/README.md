# Compactness repair diagnostics

The private measure cast in `TauCeti.Analysis.Sobolev.RellichKondrachov` now transports the Lᵖ vector directly, avoiding computed projections through a cast of an entire isometry structure. Its norm and representative identities are proved, and public statements are unchanged.

On November 2, 2026, the complete local build after this repair passed in 188.5 seconds and the 722-declaration axiom audit passed in 10.5 seconds. The parent directory contains the latest rebuild and audit after the subsequent Green-interface repair. `affected-types.log` records exact compiled-type matches for all 18 selections in the ten compactness-dependent configurations.

`paranoid-module.json` and its log record a successful 21.6-second run of the bundled Lean 4.35.0 paranoid kernel on macOS. This is module-only replay with compiled imports trusted. It does not count toward the required sandboxed Linux Comparator coverage or replace the other five kernels.

`full-export-kernels.json` and the six accompanying logs record a stronger local preflight: every bundled kernel accepted the exported `dirichlet_compactness` solution, including its transitive proof dependencies and Comparator primitives. The default and paranoid Lean kernels took 69.8 and 66.6 seconds; lean4lean took 76.0 seconds; nanoda, con-leche and con-ron took 13.3, 13.4 and 9.3 seconds. These runs used macOS, did not perform the challenge comparison and were not sandboxed. They remain diagnostic evidence and are excluded from CI coverage.
