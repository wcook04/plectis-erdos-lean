/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CarrySurvivorExtinction`, `Erdos249257.DiagonalPincerCertificatesT64`,
`Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.Erdos249.PaperCompleteR21.DiagonalCertificateTableScales`,
`ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts`.
-/

open Finset

namespace Erdos249257.ExternalVerification249PaperStructuresN

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

/-- States prop:deposits from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.certifiedKill_diagonal_t64 in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_diagonal_t64 :
    certifiedKill (periodLcm 64) (periodLcm 64) 93 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_diagonal_t64_paper in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem certifiedKill_diagonal_t64_paper :
    certifiedKill (periodLcm 64) (periodLcm 64) 93 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_single_witness_six_ninetyThree in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem shortWindowSupply_single_witness_six_ninetyThree (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    a₀ ≤ 6 ∧ (93 : ℕ) < 2 * 2 ^ 6 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_witness_eq_t64_certificate in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem shortWindowSupply_witness_eq_t64_certificate :
    certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ↔
      certifiedKill (periodLcm 64) (periodLcm 64) 93 := by
  sorry

end Erdos249257.ExternalVerification249PaperStructuresN
