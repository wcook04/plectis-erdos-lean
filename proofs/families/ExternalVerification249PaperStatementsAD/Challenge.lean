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
`Erdos249257.CarrySurvivorExtinction`, `Erdos249257.FirstHarmonicPivot`,
`Erdos249257.LcmConeFlatness`, `Erdos249257.PivotAntiReconstruction`,
`Erdos249257.TotientTailPeriodKiller`.
-/

open Finset

namespace Erdos249257.ExternalVerification249PaperStatementsAD

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))

noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)

noncomputable def DTWWindowSeparatedPairsAt (h : ℕ) : Prop :=
  ∀ X₀ : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      ∃ P : Finset (ℕ × ℕ), ∃ δ : ℝ,
      max X₀ 1 ≤ X ∧
      T.Nonempty ∧
      T ⊆ Finset.Ico X (2 * X) ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      P ⊆ T.product T ∧
      0 ≤ δ ∧
      (∀ p ∈ P,
        δ ≤ ‖windowFirstExp h p.1 L - windowFirstExp h p.2 L‖) ∧
      2 * (T.card : ℝ) ^ 2 / 5 ≤ (P.card : ℝ) * δ ^ 2

noncomputable def DTWWindowSeparatedPairs : Prop :=
  ∀ h : ℕ, 0 < h → DTWWindowSeparatedPairsAt h

noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

/-- States prop:deposits from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.certifiedKill_all_upto_sixteen in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedKill_all_upto_sixteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9 := by
  sorry

/-- States catalogue:cert:a5, prop:A5-inv from the long record for Erdős problem #249.
Transported from Erdos249257.TotientTailPeriodKiller.certifiedKill_depth_floor in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem certifiedKill_depth_floor {h N L : ℕ} (hcert : certifiedKill h N L) :
    (2 * (N + h + L + 2) : ℤ) < 2 ^ L := by
  sorry

/-- States prop:iffs from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.dtwWindowSeparatedPairs_iff_irrational_totient_series in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem dtwWindowSeparatedPairs_iff_irrational_totient_series :
    DTWWindowSeparatedPairs ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States catalogue:cert:a7 from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.exists_certifiedKill_iff_tail_diff_notMem_int in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_certifiedKill_iff_tail_diff_notMem_int (h N : ℕ) :
    (∃ L, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States catalogue:cert:b8 from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_all_tail_diffs_nonintegral
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem irrational_totient_series_iff_all_tail_diffs_nonintegral :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States catalogue:cert:a10, prop:A10, prop:iffs from the long record for Erdős problem #249.
Transported from
Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_certificate_supply in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L := by
  sorry

/-- States catalogue:cert:a8 from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.tail_diff_int_of_den_dvd in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_diff_int_of_den_dvd (r : ℚ)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (r : ℝ))
    (h N : ℕ) (hdvd : (r.den : ℕ) ∣ 2 ^ N * (2 ^ h - 1)) :
    totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States catalogue:cert:a2 from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.tail_diff_mem_int_iff_scaled_series_mem_int in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tail_diff_mem_int_iff_scaled_series_mem_int (h N : ℕ) :
    (totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ↔
    ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      ∈ Set.range ((↑) : ℤ → ℝ)) := by
  sorry

/-- States catalogue:cert:a6 from the long record for Erdős problem #249. Transported from
Erdos249257.TotientTailPeriodKiller.tail_diff_notMem_int_of_certifiedKill in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_diff_notMem_int_of_certifiedKill {h N L : ℕ} (hcert : certifiedKill h N L) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States catalogue:cert:a2, prop:shift from the long record for Erdős problem #249.
Transported from Erdos249257.TotientTailPeriodKiller.two_pow_mul_totient_series_eq in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem two_pow_mul_totient_series_eq (N : ℕ) :
    (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (totientPrefix N : ℝ) + totientTail N := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsAD
