# Three-prime running-LCM kernel verification

`FC269UniformKernelSolution.lean` proves the exact statement intended for
`FormalConjectures/Paper/ThreePrimeRunningLcm.lean`, including the uniform
minor and finite nonseparation clauses.

The adapter composes the two original `KernelCarryRank` theorems. Its three
transitive source modules are copied unchanged from the selected source commit;
`source-binding.json` records those hashes and the historical proof evidence.
The isolated project adapts the existing `FC1049HankelCurrent` Lake configuration
to Formal Conjectures' Lean4.33.1 environment.

Build this exact target with `lake --wfail build FC269UniformKernelSolution`.
Local compilation and actual receiving-export verification are still pending.
The old official proof and receiving build retain their original source pins.

- `FC269UniformKernelSolution.lean`: destination definitions and exact theorem adapter.
- `ErdosProblems/Erdos269/KernelCarryRank.lean`: uniform rank and nonseparation proof.
- `ErdosProblems/Erdos269/ThreePrimeRunningLcm.lean`: genuine running-LCM vocabulary.
- `ErdosProblems/Shared/IrrationalRotationStaircase.lean`: irrational rotation prerequisite.
- `lean-toolchain`, `lakefile.toml`, `lake-manifest.json`: isolated pinned environment.
