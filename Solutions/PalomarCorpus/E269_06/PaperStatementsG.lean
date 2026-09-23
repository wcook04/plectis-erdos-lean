/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.DyadicBlockMassIdentity
import ErdosProblems.Erdos269.DyadicBlockThresholdPartition
import ErdosProblems.Erdos269.DyadicOrderedTailRecurrence
import ErdosProblems.Erdos269.DyadicShellSummability
import ErdosProblems.Erdos269.IntegralBranchExtinction
import ErdosProblems.Erdos269.JumpConstraintMajorant
import ErdosProblems.Erdos269.PaperCompleteR20.RealBoundDenominatorReduction
import ErdosProblems.Erdos269.PaperExactDenominatorR13
import ErdosProblems.Erdos269.PaperR7SeriesIdentification
import ErdosProblems.Erdos269.PaperR7WindowResults
import ErdosProblems.Erdos269.RationalLatticeReduction
import ErdosProblems.Erdos269.ResidueEscape
import ErdosProblems.Erdos269.RestrictedFloorSum
import ErdosProblems.Erdos269.ThreePrimeRunningLcm
import Solutions.PalomarCorpus.E269_06.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStatementsG
export PalomarCorpus.E269_06.Shared (DyadicInternalPower actualWindowBase dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicOrderedBlockDigit235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell windowBase)

noncomputable def ClearingCondition (u v w a : ℕ) : Prop :=
  1 ≤ a ∧ 2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a

noncomputable def clearingCondition_sufficient (u v w : ℕ) :
    ClearingCondition u v w (u + 1 + 2 * v + 3 * w) := by
  let aD := u + 1 + 2 * v + 3 * w
  have h2 : 2 ^ (u + 1) ≤ 2 ^ aD :=
    Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega)
  have h3four : 3 ^ v ≤ 4 ^ v := Nat.pow_le_pow_left (by norm_num) v
  have h4two : 4 ^ v = 2 ^ (2 * v) := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
  have h3 : 3 ^ v ≤ 2 ^ aD := by
    rw [h4two] at h3four
    exact h3four.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  have h5eight : 5 ^ w ≤ 8 ^ w := Nat.pow_le_pow_left (by norm_num) w
  have h8two : 8 ^ w = 2 ^ (3 * w) := by
    rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul]
  have h5 : 5 ^ w ≤ 2 ^ aD := by
    rw [h8two] at h5eight
    exact h5eight.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [aD]; omega))
  exact ⟨by omega, h2, h3, h5⟩

noncomputable def firstClearingIndex (u v w : ℕ) : ℕ := by
  classical
  exact Nat.find ⟨u + 1 + 2 * v + 3 * w, clearingCondition_sufficient u v w⟩

noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)

noncomputable def dyadicSmoothWindowMassQ235 (start count : ℕ) : ℚ :=
  ∑ i ∈ Finset.range count, dyadicShellMassQ235 (start + i)

noncomputable def heightNormalizer235 (a : ℕ) : ℕ :=
  threePrimeHeight 2 3 5 (2 ^ a) / 2

noncomputable def rationalTailState (N : ℤ) (D a : ℕ) : ℚ :=
  (heightNormalizer235 a : ℚ) *
    ((N : ℚ) / (D : ℚ) - 1 - dyadicSmoothWindowMassQ235 1 (a - 1))

noncomputable abbrev Exponent235 := ℕ × ℕ × ℕ

noncomputable def ShortPaperEscape : Prop :=
  ∀ B : ℕ, 0 < B → Nat.Coprime B 30 → ∀ a₀ : ℕ, 1 ≤ a₀ →
    ∃ lo len : ℕ, a₀ ≤ lo ∧ 0 < len ∧
      90 * B * (lo + len + 1) ^ 2 <
        leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
          (-((B : ℤ) * actualWindowForcing lo len))

noncomputable def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2

noncomputable def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}

noncomputable def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x

noncomputable def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2

noncomputable def smoothReciprocal235 (x : Smooth235) : ℝ :=
  (smoothPrefixLcm 2 3 5 x.val : ℝ)⁻¹

noncomputable def paperSeries235 : ℝ := ∑' x : Smooth235, smoothReciprocal235 x

noncomputable def dyadicNormalizedTailStateR235 (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a

noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a

noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)

noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a

theorem conditional_denominator_reduction_real_bound
    (c d b m : ℕ → ℤ) (s B : ℤ) (hs : 0 < s)
    (hfactor : ∀ n, c n = s * d n)
    (hrec : ∀ n, c (n + 1) = b n * c n - (s * B) * m n) :
    (∀ n, d (n + 1) = b n * d n - B * m n) ∧
    (∀ lo len, d (lo + len) = windowBase b lo len * d lo -
      B * windowForcing b m lo len) ∧
    (∀ n (t : ℝ),
      (0 < c n ∧ (c n : ℝ) ≤ ((s * B : ℤ) : ℝ) * t) ↔
        (0 < d n ∧ (d n : ℝ) ≤ (B : ℝ) * t)) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos269.PaperCompleteR20.conditional_denominator_reduction_real_bound c d b m s B hs hfactor hrec

theorem exact_denominators_and_minimal_clearing
    {N : ℤ} {u v w B a : ℕ}
    (hB : 0 < B) (hB30 : Nat.Coprime B 30)
    (hcop : Nat.Coprime N.natAbs (2 ^ u * 3 ^ v * 5 ^ w * B))
    (ha : 1 ≤ a)
    (hval : paperSeries235 =
      (N : ℝ) / ((2 ^ u * 3 ^ v * 5 ^ w * B : ℕ) : ℝ)) :
    ((rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a : ℚ) : ℝ) =
        trueNormalizedState a ∧
      (rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w * B) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      ((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den =
        (2 ^ u * 3 ^ v * 5 ^ w) /
          Nat.gcd (2 ^ u * 3 ^ v * 5 ^ w) (heightNormalizer235 a) ∧
      (((B : ℚ) * rationalTailState N (2 ^ u * 3 ^ v * 5 ^ w * B) a).den = 1 ↔
        firstClearingIndex u v w ≤ a) := @ErdosProblems.Erdos269.PaperR13.exact_denominators_and_minimal_clearing N u v w B a hB hB30 hcop ha hval

theorem long_no_bounded_length {B H : ℕ} (hB : 0 < B)
    (_hcop : Nat.Coprime B 30) (_hH : 1 ≤ H) :
    Set.Finite {lo : ℕ | ∃ len : ℕ, 1 ≤ len ∧ len ≤ H ∧
      longPaperCap B (lo + len) <
        leastPositiveResidue (Int.natAbs (actualWindowBase lo len))
          (-((B : ℤ) * actualWindowForcing lo len))} := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos269.PaperR7.long_no_bounded_length B H hB _hcop _hH

theorem short_window_equivalence :
    Irrational paperSeries235 ↔ ShortPaperEscape := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos269.PaperR7.short_window_equivalence

end PalomarCorpus.E269.PaperStatementsG
