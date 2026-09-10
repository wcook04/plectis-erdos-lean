/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos243.PaperCompleteR8.CanonicalNegativeMass
import Mathlib
import ErdosProblems.Erdos243.SparseResetRecovery
import Solutions.PalomarCorpus.E243.Shared

open scoped BigOperators
open Finset

/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

namespace PalomarCorpus.E243.SummableNegativeMassRigidity
export PalomarCorpus.E243.Shared (centeredState sylvesterNext)

noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D

noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D

noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n

theorem summableNegativeMass_completeRigidity
    (a D : ℕ → ℤ) (C : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, (C (n + 1) : ℤ) = nextTailState (a n) (D n) (C n))
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) =
      (C n : ℤ) - centeredState (a n) (D n) (C n))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (centeredState (a n) (D n) (C n)) < C n)
    (hsum : Summable (negativeRelativeMass C
      (fun n ↦ centeredState (a n) (D n) (C n)))) :
    (∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0) ∧
      ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := by
  have hD' : ∀ n, D (n + 1) =
      ErdosProblems.Erdos243.nextDenState (a n) (D n) := by
    simpa [nextDenState, ErdosProblems.Erdos243.nextDenState] using hD
  have hC' : ∀ n, (C (n + 1) : ℤ) =
      ErdosProblems.Erdos243.nextTailState (a n) (D n) (C n) := by
    simpa [nextTailState, ErdosProblems.Erdos243.nextTailState] using hC
  have hstep' : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) -
      ErdosProblems.Erdos243.centeredState (a n) (D n) (C n) := by
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hstep
  have hvanish' : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs
        (ErdosProblems.Erdos243.centeredState (a n) (D n) (C n)) < C n := by
    simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hvanish
  have hsum' : Summable
      (ErdosProblems.Erdos243.negativeRelativeMass C
        (fun n ↦ ErdosProblems.Erdos243.centeredState (a n) (D n) (C n))) := by
    simpa [negativeRelativeMass,
      ErdosProblems.Erdos243.negativeRelativeMass, centeredState,
      ErdosProblems.Erdos243.centeredState] using hsum
  have hzero' : ∃ N, ∀ n, N ≤ n →
      ErdosProblems.Erdos243.centeredState (a n) (D n) (C n) = 0 :=
    ErdosProblems.Erdos243.eventually_zero_of_summable_negativeRelativeMass
      C (fun n ↦ ErdosProblems.Erdos243.centeredState (a n) (D n) (C n))
      hCpos hstep' hvanish' hsum'
  have hrec' : ∃ N, ∀ n, N ≤ n →
      a (n + 1) = ErdosProblems.Erdos243.sylvesterNext (a n) :=
    ErdosProblems.Erdos243.sylvesterNext_eventually_of_summable_negativeRelativeMass
      a D C hD' hC' hCpos hstep' hvanish' hsum'
  constructor
  · simpa [centeredState, ErdosProblems.Erdos243.centeredState] using hzero'
  · simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using hrec'

noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n

theorem finite_negative_mass_scalar (C : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n)
    (hsum : Summable (negativeRelativeMass C E)) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  exact ErdosProblems.Erdos243.eventually_zero_of_summable_negativeRelativeMass_scalar C E hCpos hstep hsum

theorem canonical_finite_negative_mass
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hmass : Summable (fun n =>
      max (-(centeredState (a n : ℤ) (canonicalDenominator a q n : ℤ)
        (canonicalNaturalNumerator a p q n : ℤ) : ℝ)) 0 /
          (canonicalNaturalNumerator a p q n : ℝ))) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  exact ErdosProblems.Erdos243.PaperCompleteR8.canonical_sylvester_of_finite_negative_mass a hpos p q hq hs hmass

end PalomarCorpus.E243.SummableNegativeMassRigidity
