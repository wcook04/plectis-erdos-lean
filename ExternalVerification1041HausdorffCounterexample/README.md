# Preconnected-set Hausdorff comparison for Erdős 1041

The selected theorem says that one monic degree-seven complex polynomial has
distinct roots in the open unit disc, and every preconnected subset of its
strict unit lemniscate containing two distinct roots has one-dimensional
Hausdorff measure greater than two. `Challenge.lean` states the result from
Mathlib alone. `Solution.lean` applies the public source theorem
`Erdos1041.Counterexample.erdos1041_counterexample_hausdorff` to the explicit
polynomial from the same source closure. The two other Hausdorff forms in the
short and long papers already have an E1041_01 hosted Comparator receipt, and
the total-variation instance has an E1041_07 receipt. This new comparison
selects only the preconnected-set theorem missing from those receipts.

`source_binding.json` records the twelve-module Lean 4.30 source closure and
environment. `check_contract.py --source-root . --self-test` checks the exact
source hashes, the independent Challenge statement, the selected configuration,
and seven deliberate corruptions. The hosted replay rebuilds Challenge and
Solution, prints the selected axiom set, and runs the pinned Comparator with
NanoDa and the Lean default kernel in the supported systemd sandbox. A second
Solution drops the root `Nodup` conjunct; it must fail with the exact
statement-mismatch diagnostic and neither kernel acceptance.

This candidate does not formalise ani's whole small-parameter family and does
not adjudicate the historical wording. No paper Comparator status changes on
source preparation alone; that requires a successful exact-head hosted replay
and binding of all four declarations in each paper row.
