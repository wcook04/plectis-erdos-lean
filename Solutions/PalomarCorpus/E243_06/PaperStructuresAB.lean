/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser
import ErdosProblems.Erdos243.PaperCompleteR21.ExactOrbitRecordDichotomy
import ErdosProblems.Erdos243.ReciprocalTailRigidity
import Solutions.PalomarCorpus.E243_06.Statement

open Filter

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.PaperStructuresAB
export PalomarCorpus.E243_06.Shared (centeredState recordLogLog)

theorem exactOrbit_unbounded_of_error_not_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∀ H : ℕ, ∃ n, H ≤ C n := @ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_unbounded_of_error_not_eventually_zero a C D E hC hD hE hvanish hnot

theorem exists_multiplier_ge_four (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (M : ℕ) :
    ∃ t, M ≤ t ∧ N ≤ t ∧ 4 ≤ a t := @ErdosProblems.Erdos243.PaperCompleteR21.exists_multiplier_ge_four a C D E ha hCpos hD0 hC hD hE N hN M

theorem slowNegative_eventually_zero_and_sylvesterNext_unconditional
    (a C D : ℕ → ℕ) (E : ℕ → ℤ) (δ : ℝ)
    (ha : ∀ n, 1 < a n)
    (hCpos : ∀ n, 0 < C n)
    (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hDstep : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hδ0 : 0 < δ) (hδ1 : δ < 1)
    (hslow : ∃ N, ∀ n, N ≤ n → E n < 0 →
      -((E n : ℤ) : ℝ) ≤ (1 - δ) * recordLogLog ((C n : ℕ) : ℝ)) :
    (∃ N, ∀ n, N ≤ n → E n = 0) ∧
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := @ErdosProblems.Erdos243.PaperCompleteR21.slowNegative_eventually_zero_and_sylvesterNext_unconditional a C D E δ ha hCpos hD0 hC hDstep hE hvanish hδ0 hδ1 hslow

theorem tail_binaryTower_lower (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (h4 : 4 ≤ a N) :
    ∀ k, 2 * binaryTower k ≤ a (N + k) := @ErdosProblems.Erdos243.PaperCompleteR21.tail_binaryTower_lower a C D E ha hCpos hC hD hE N hN h4

end PalomarCorpus.E243.PaperStructuresAB
