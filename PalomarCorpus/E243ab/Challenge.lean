/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band b

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open Filter

namespace PalomarCorpus.E243.PaperStructuresAB
open Filter
/-- An integer height which the paper's normaliser sends to its index. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.binaryTower, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryTower (n : ℕ) : ℕ := 2 ^ (2 ^ n)
/-- The exact real-valued normaliser from the inclusive boundary. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_unbounded_of_error_not_eventually_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exactOrbit_unbounded_of_error_not_eventually_zero
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    ∀ H : ℕ, ∃ n, H ≤ C n := by
  sorry
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.exists_multiplier_ge_four in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_multiplier_ge_four (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (M : ℕ) :
    ∃ t, M ≤ t ∧ N ≤ t ∧ 4 ≤ a t := by
  sorry
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.slowNegative_eventually_zero_and_sylvesterNext_unconditional in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.tail_binaryTower_lower in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_binaryTower_lower (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (N : ℕ) (hN : ∀ n, N ≤ n → 4 * Int.natAbs (E n) < C n) (h4 : 4 ≤ a N) :
    ∀ k, 2 * binaryTower k ≤ a (N + k) := by
  sorry
end PalomarCorpus.E243.PaperStructuresAB
