# Frozen Formal Conjectures proof projects

These isolated projects preserve the complete local import closure of an original
proof and its original Lake configuration, dependency lock and Lean toolchain.
Their source files keep the original relative layout and bytes. The main release
project does not import these historical projects. When a selected module also
names a Lake library, its target builds every configured library glob. The frozen
snapshot includes those roots and their complete import closure too. Expanded
packets record `proof_source_closure` separately from all immutable build inputs
in `source_closure`; a co-built sibling is not another selected proof target.

| Project | Original source commit | Formal Conjectures PRs | Official caller |
| --- | --- | --- | --- |
| [FC257ReciprocalSupport](FC257ReciprocalSupport/source-binding.json) | `598cd7bac8b73dcfef3687f46922c1ef6da766ae` | 6529 | [Workflow](../.github/workflows/fc257-reciprocal-trusted-preflight.yml) |
| [FC249RationalObservable](FC249RationalObservable/source-binding.json) | `c4bff4aa152465b3c92fffe808f76b0e5f78293c` | 6579 | [Workflow](../.github/workflows/fc249-rational-trusted-preflight.yml) |
| [FCMergedIntegerAdapters](FCMergedIntegerAdapters/source-binding.json) | `b9f1eb80aa11bbf66fb1df88804502b8c9c27d8e` | 6506, 6507, 5034 | [Workflow](../.github/workflows/fc-merged-integer-trusted-preflight.yml) |
| [FC1041HausdorffCounterexample](FC1041HausdorffCounterexample/source-binding.json) | `0ee31b3a99ef93d2b679a427b474b23710597bad` | 6505 | [Workflow](../.github/workflows/fc1041-hausdorff-trusted-preflight.yml) |

Each manifest records the original repository, exact origin paths and hashes for
every copied source. New Challenge files state the selected targets independently
using Mathlib. Their deliberate `sorry` holes specify trusted statements, and do
not provide proof evidence. The selected Solution is the original source module.

Check the source packaging without running any candidate Lean code:

```sh
python3 scripts/check_frozen_fc_projects.py --project verification/FC257ReciprocalSupport
```

This checks recorded bytes and the complete local import closure. It establishes
no kernel acceptance. Certification requires a full successful official verifier
job tied to the exact replay-host commit, selected project and declarations. The
pinned official workflow prepares dependencies and protects its compiled Challenge
before executing the candidate. Historical CI runs at another source commit,
shared-workspace replay logs, and green packaging checks cannot substitute for that
report. Registry verification and registration remain separate outcomes.

The third merged target uses the `b9f1eb8` original module. That module is byte-identical
to the older `a9104f2` file linked by PR 5034, as recorded in its manifest; a new
verification report certifies only the new replay-host source commit.
