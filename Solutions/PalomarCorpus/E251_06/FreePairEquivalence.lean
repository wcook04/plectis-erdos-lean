/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.FreePairReduction
import Solutions.PalomarCorpus.E251_06.Statement

open scoped BigOperators

namespace PalomarCorpus.E251.FreePairEquivalence
export PalomarCorpus.E251_06.Shared (DyadicTailRecurrence RatIntegral RealDyadicTailRecurrence RealIntegral prime0 primeGap0 primeGapDyadicTerm realTailShift)

theorem irrational_primeGap_tsum_iff_cofinalFreePairNonintegral :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral primeGapRealTail :=
  ErdosProblems.Erdos251.irrational_primeGap_tsum_iff_cofinalFreePairNonintegral

theorem irrational_initial_iff_cofinalFreePairNonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔ CofinalFreePairNonintegral T :=
  ErdosProblems.Erdos251.irrational_initial_iff_cofinalFreePairNonintegral hrec

theorem cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts
    {g : ℕ → ℤ} {T : ℕ → ℝ} (hrec : RealDyadicTailRecurrence g T) :
    CofinalFreePairNonintegral T ↔ CofinalNonintegralTailShifts T :=
  ErdosProblems.Erdos251.cofinalFreePairNonintegral_iff_cofinalNonintegralTailShifts hrec

theorem exists_free_pair_lattice {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    ∃ N₀ t : ℕ, 0 < t ∧ ∀ N M : ℕ, N₀ ≤ N → N₀ ≤ M →
      (RatIntegral (T M - T N) ↔ N ≡ M [MOD t]) :=
  ErdosProblems.Erdos251.exists_free_pair_lattice hrec

theorem free_pair_integral_iff_modEq {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) {N₀ : ℕ} (hodd : Odd (T N₀).den)
    {N M : ℕ} (hN : N₀ ≤ N) (hM : N₀ ≤ M) :
    RatIntegral (T M - T N) ↔ N ≡ M [MOD orderOf (2 : ZMod (T N₀).den)] :=
  ErdosProblems.Erdos251.free_pair_integral_iff_modEq hrec hodd hN hM

theorem primeGapRealTail_recurrence :
    RealDyadicTailRecurrence (fun n => (primeGap0 n : ℤ)) primeGapRealTail :=
  ErdosProblems.Erdos251.primeGapRealTail_recurrence

theorem primeGapRealTail_zero :
    primeGapRealTail 0 = 2 * (∑' n : ℕ, primeGapDyadicTerm n) - 1 :=
  ErdosProblems.Erdos251.primeGapRealTail_zero

end PalomarCorpus.E251.FreePairEquivalence
