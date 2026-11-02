# Compactness repair diagnostics

The private measure cast in `TauCeti.Analysis.Sobolev.RellichKondrachov` now transports the Lᵖ vector directly, avoiding computed projections through a cast of an entire isometry structure. Its norm and representative identities are proved, and public statements are unchanged.

On November 2, 2026, the complete local build passed in 188.5 seconds and the 722-declaration axiom audit passed in 10.5 seconds. Their records are in the parent directory. `affected-types.log` records exact compiled-type matches for all 18 selections in the ten affected configurations.

`paranoid-module.json` and its log record a successful 21.6-second run of the bundled Lean 4.35.0 paranoid kernel on macOS. This is module-only replay with compiled imports trusted. It does not count toward the required sandboxed Linux Comparator coverage or replace the other five kernels.
