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
`Erdos249257.CarrySurvivorExtinction`, `Erdos249257.LcmConeFlatness`,
`Erdos249257.LcmDiagonalReduction`, `Erdos249257.TotientActualLcmOrbitSign`,
`Erdos249257.TotientTailPeriodKiller`.
-/

open Finset

namespace Erdos249257.ExternalVerification249PaperStatementsA

noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)

noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

/-- States prop:sign from the long record for Erdős problem #249. Transported from
Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailDiff_shift_pos in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem actualLcmTailDiff_shift_pos
    {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 <
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J) := by
  sorry

/-- States prop:sign from the long record for Erdős problem #249. Transported from
Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcm_integral_forces_topEdgeResidue
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem actualLcm_integral_forces_topEdgeResidue
    {a J K : ℕ} (ha : 8 ≤ a)
    (hshort : J + K + (a + 6) < 2 * 2 ^ a)
    {d : ℤ}
    (hd : (d : ℝ) =
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J))
    (hroom :
      ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) <
        (2 : ℤ) ^ K) :
    let H := periodLcm (2 ^ a)
    let e := carryOrbit H (H + J) d K
    let P := (2 : ℤ) ^ K
    let B := ((2 * H + J + K + 2 : ℕ) : ℤ)
    windowDiscrepancy H (H + J) K % P = P - e ∧
      P - B < windowDiscrepancy H (H + J) K % P ∧
      windowDiscrepancy H (H + J) K % P < P := by
  sorry

/-- States prop:sign from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.carryOrbit_eq_tail_diff in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
lemma carryOrbit_eq_tail_diff {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N d i : ℝ) = totientTail (N + i + h) - totientTail (N + i) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from Erdos249257.TotientTailPeriodKiller.dvd_periodLcm in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
lemma dvd_periodLcm {h t : ℕ} (h1 : 1 ≤ h) (ht : h ≤ t) : h ∣ periodLcm t := by
  sorry

/-- States catalogue:cert:b4 from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.eq_prime_pow_of_not_dvd_periodLcm in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem eq_prime_pow_of_not_dvd_periodLcm {t j : ℕ} (hj : 0 < j) (hlt : j < 2 * t)
    (hnd : ¬ j ∣ periodLcm t) :
    ∃ p k : ℕ, Nat.Prime p ∧ j = p ^ k ∧ t < j := by
  sorry

/-- States catalogue:cert:b3, prop:B3, prop:iffs from the long record for Erdős problem #249.
Transported from
Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_lcm_diagonal_certificate_supply
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem irrational_totient_series_iff_lcm_diagonal_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
        certifiedKill (periodLcm t) (periodLcm t) L := by
  sorry

/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonintegrality_supply
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem irrational_totient_series_of_lcm_cone_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m : ℕ, 0 < q ∧
      totientTail (q * periodLcm t + m * periodLcm t) - totientTail (q * periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.periodLcm_diagonal_kill_iff_tail_diff_notMem_int in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem periodLcm_diagonal_kill_iff_tail_diff_notMem_int (t : ℕ) :
    (∃ L, certifiedKill (periodLcm t) (periodLcm t) L) ↔
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsA
