/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.LcmConeFlatness
import Erdos249257.LcmDiagonalReduction
import Erdos249257.TotientActualLcmOrbitSign
import Erdos249257.TotientTailPeriodKiller
import Solutions.PalomarCorpus.E249_10.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsA
export PalomarCorpus.E249_10.Shared (certifiedKill periodLcm totientTail windowDiscrepancy)

noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)

noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)

theorem actualLcmTailDiff_shift_pos
    {a J : ℕ} (ha : 8 ≤ a)
    (hshort : J + (a + 6) < 2 * 2 ^ a) :
    0 <
      totientTail (2 * periodLcm (2 ^ a) + J) -
        totientTail (periodLcm (2 ^ a) + J) := by
  set_option smartUnfolding false in
  exact @Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailDiff_shift_pos a J ha hshort

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
  set_option smartUnfolding false in
  exact @Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcm_integral_forces_topEdgeResidue a J K ha hshort d hd hroom

lemma carryOrbit_eq_tail_diff {h N : ℕ} {d : ℤ}
    (hd : (d : ℝ) = totientTail (N + h) - totientTail N) (i : ℕ) :
    (carryOrbit h N d i : ℝ) = totientTail (N + i + h) - totientTail (N + i) := by
  set_option smartUnfolding false in
  exact @Erdos249257.TotientTailPeriodKiller.carryOrbit_eq_tail_diff h N d hd i

lemma dvd_periodLcm {h t : ℕ} (h1 : 1 ≤ h) (ht : h ≤ t) : h ∣ periodLcm t := by
  set_option smartUnfolding false in
  exact @Erdos249257.TotientTailPeriodKiller.dvd_periodLcm h t h1 ht

theorem eq_prime_pow_of_not_dvd_periodLcm {t j : ℕ} (hj : 0 < j) (hlt : j < 2 * t)
    (hnd : ¬ j ∣ periodLcm t) :
    ∃ p k : ℕ, Nat.Prime p ∧ j = p ^ k ∧ t < j := by
  set_option smartUnfolding false in
  exact @Erdos249257.TotientTailPeriodKiller.eq_prime_pow_of_not_dvd_periodLcm t j hj hlt hnd

theorem irrational_totient_series_iff_lcm_diagonal_certificate_supply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L,
        certifiedKill (periodLcm t) (periodLcm t) L := by
  set_option smartUnfolding false in
  exact @Erdos249257.TotientTailPeriodKiller.irrational_totient_series_iff_lcm_diagonal_certificate_supply

theorem irrational_totient_series_of_lcm_cone_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ q m : ℕ, 0 < q ∧
      totientTail (q * periodLcm t + m * periodLcm t) - totientTail (q * periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  set_option smartUnfolding false in
  exact @Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_cone_nonintegrality_supply hsupply

theorem irrational_totient_series_of_lcm_diagonal_nonintegrality_supply
    (hsupply : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  set_option smartUnfolding false in
  exact @Erdos249257.TotientTailPeriodKiller.irrational_totient_series_of_lcm_diagonal_nonintegrality_supply hsupply

theorem periodLcm_diagonal_kill_iff_tail_diff_notMem_int (t : ℕ) :
    (∃ L, certifiedKill (periodLcm t) (periodLcm t) L) ↔
      totientTail (periodLcm t + periodLcm t) - totientTail (periodLcm t)
        ∉ Set.range ((↑) : ℤ → ℝ) := by
  set_option smartUnfolding false in
  exact @Erdos249257.TotientTailPeriodKiller.periodLcm_diagonal_kill_iff_tail_diff_notMem_int t

end PalomarCorpus.E249.PaperStatementsA
