/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.FirstHarmonicPivot
import Erdos249257.LcmConeFlatness
import Erdos249257.PivotAntiReconstruction
import Erdos249257.TotientTailPeriodKiller
import Solutions.PalomarCorpus.E249_06.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAD
export PalomarCorpus.E249_06.Shared (certifiedKill totientTail windowDiscrepancy)

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

noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)

theorem certifiedKill_all_upto_sixteen :
    ∀ h ∈ Finset.Icc 1 16, certifiedKill h 14 9 := @Erdos249257.TotientTailPeriodKiller.certifiedKill_all_upto_sixteen

theorem certifiedKill_depth_floor {h N L : ℕ} (hcert : certifiedKill h N L) :
    (2 * (N + h + L + 2) : ℤ) < 2 ^ L := @Erdos249257.TotientTailPeriodKiller.certifiedKill_depth_floor h N L hcert

theorem dtwWindowSeparatedPairs_iff_irrational_totient_series :
    DTWWindowSeparatedPairs ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := @Erdos249257.TotientTailPeriodKiller.dtwWindowSeparatedPairs_iff_irrational_totient_series

theorem exists_certifiedKill_iff_tail_diff_notMem_int (h N : ℕ) :
    (∃ L, certifiedKill h N L) ↔
      totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := @Erdos249257.TotientTailPeriodKiller.exists_certifiedKill_iff_tail_diff_notMem_int h N

theorem irrational_totient_series_iff_all_tail_diffs_nonintegral :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N : ℕ,
        totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := @Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_all_tail_diffs_nonintegral

theorem irrational_totient_series_iff_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ,
        ∃ N, N₀ ≤ N ∧ ∃ L, certifiedKill h N L := @Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_certificate_supply

theorem tail_diff_int_of_den_dvd (r : ℚ)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) = (r : ℝ))
    (h N : ℕ) (hdvd : (r.den : ℕ) ∣ 2 ^ N * (2 ^ h - 1)) :
    totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ) := @Erdos249257.TotientTailPeriodKiller.tail_diff_int_of_den_dvd r hS h N hdvd

theorem tail_diff_mem_int_iff_scaled_series_mem_int (h N : ℕ) :
    (totientTail (N + h) - totientTail N ∈ Set.range ((↑) : ℤ → ℝ)) ↔
    ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
        (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      ∈ Set.range ((↑) : ℤ → ℝ)) := @Erdos249257.TotientTailPeriodKiller.tail_diff_mem_int_iff_scaled_series_mem_int h N

theorem tail_diff_notMem_int_of_certifiedKill {h N L : ℕ} (hcert : certifiedKill h N L) :
    totientTail (N + h) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := @Erdos249257.TotientTailPeriodKiller.tail_diff_notMem_int_of_certifiedKill h N L hcert

theorem two_pow_mul_totient_series_eq (N : ℕ) :
    (2 : ℝ) ^ N * (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
      = (totientPrefix N : ℝ) + totientTail N := @Erdos249257.TotientTailPeriodKiller.two_pow_mul_totient_series_eq N

end PalomarCorpus.E249.PaperStatementsAD
