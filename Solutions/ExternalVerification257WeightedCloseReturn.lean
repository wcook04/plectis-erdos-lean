/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.PaperCompleteR8.WeightedReturn

set_option autoImplicit false

noncomputable section
namespace Erdos249257.ExternalVerification257WeightedCloseReturn
open Filter Topology
open scoped BigOperators

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p

def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))

def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))

noncomputable def shiftedRadixAtom (b N d : ℕ) : ℝ :=
  if d = 0 then 0
  else (b : ℝ) ^ (N % d) / ((b : ℝ) ^ d - 1)

noncomputable def shiftedRadixSupportAtom
    (b : ℕ) (A : Set ℕ) (N d : ℕ) : ℝ :=
  Set.indicator A (shiftedRadixAtom b N) d

def displacement (b : ℕ) (A : Set ℕ) (N : ℕ) : ℝ :=
  (∑' d : ℕ, shiftedRadixSupportAtom b A N d) - erdosSupportSeries b A

theorem weighted_displacement_cofinal_close_return
    (b : ℕ) (E : Set ℕ) (hb : 2 ≤ b) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted b E) (hInf : E.Infinite)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < displacement b E m ∧ displacement b E m < ε := by
  simpa only [erdosSupportSeries, primeSetPart, primeWeightedTerm, FinitePrimeWeighted, shiftedRadixAtom, shiftedRadixSupportAtom, displacement, Erdos257PeriodNoncollapse.erdosSupportSeries, Erdos257PeriodNoncollapse.shiftedRadixAtom, Erdos257PeriodNoncollapse.shiftedRadixSupportAtom, ErdosProblems.Erdos257.PaperCompleteR7.primeSetPart, ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm, ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted, ErdosProblems.Erdos257.PaperCompleteR7.displacement] using
    ErdosProblems.Erdos257.PaperCompleteR8.weighted_displacement_cofinal_close_return b E hb hE0 hE hInf ε hε N

end Erdos249257.ExternalVerification257WeightedCloseReturn
end
