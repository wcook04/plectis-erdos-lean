/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR21.RecordJumpEnergySeries`,
`ErdosProblems.Erdos243.PaperCompleteR21.WindowAvoidance`.
-/

open Filter
open scoped BigOperators
open scoped Topology

namespace Erdos249257.ExternalVerification243PaperStatementsD

noncomputable def ellScale (x : ℝ) : ℝ := Real.logb 2 (Real.logb 2 (max 4 x))

/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.energy_window_real_bound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energy_window_real_bound {pr P K X : ℝ}
    (hpr : 3 ≤ pr) (hPsq : pr * pr ≤ P) (hP16 : 16 * pr ≤ P)
    (hK : 0 ≤ K) (hX : 0 ≤ X)
    (hineq : P ≤ (8 * pr + 8) * K + 4 * X + 8 * pr) :
    (1 : ℝ) / 16 ≤ K / Real.sqrt (P / 2) + X / (P / 2) := by
  sorry

/-- States long243:res:coprimalitycap from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.exists_avoiding_in_window in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_avoiding_in_window
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    {x L : ℕ} (hx : 1 ≤ x) (hL : 1 ≤ L)
    (hkL : ((({i | m i ≤ x + L} : Set ℕ).ncard : ℝ)) / (1 - θ) < (L : ℝ)) :
    ∃ n, x ≤ n ∧ n < x + L ∧ ∀ i, ¬ m i ∣ n := by
  sorry

/-- States long243:res:coprimalitycap from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.exists_slow_rise_avoiding_sequence in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_slow_rise_avoiding_sequence
    {m : ℕ → ℕ} (hmono : StrictMono m) (hm2 : ∀ i, 2 ≤ m i)
    (hcop : ∀ i j, i ≠ j → Nat.Coprime (m i) (m j))
    {θ : ℝ} (hsum : Summable fun i => (1 : ℝ) / (m i : ℝ))
    (hθ : ∑' i, (1 : ℝ) / (m i : ℝ) = θ) (hθ1 : θ < 1)
    (hscale : ∃ C : ℝ, ∀ i, |ellScale (m i : ℝ) - (i : ℝ)| ≤ C)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (T : ℕ) (u : ℕ → ℕ), StrictMono u ∧ (∀ n, 0 < u n) ∧
      (∀ i, T ≤ i → ∀ n, ¬ m i ∣ u n) ∧
      ∀ᶠ n in atTop, ((u (n + 1) : ℝ) - (u n : ℝ)) ≤ (1 + ε) * ellScale (u n : ℝ) := by
  sorry

/-- States long243:res:variablerise from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.exists_sparse_prime_coprime_sequence in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_sparse_prime_coprime_sequence :
    ∃ (p : ℕ → ℕ) (u : ℕ → ℕ),
      StrictMono p ∧ (∀ i, Nat.Prime (p i)) ∧
      StrictMono u ∧ (∀ n, 0 < u n) ∧ Tendsto u atTop atTop ∧
      (∀ i n, Nat.Coprime (u n) (p i)) ∧
      (∃ Cst : ℝ, ∀ n, ((u (n + 1) : ℝ) - (u n : ℝ))
          ≤ Cst * Real.sqrt (Real.log (Real.log ((u n : ℝ) + Real.exp (Real.exp 1))))) ∧
      Tendsto (fun n => ((u (n + 1) : ℝ) - (u n : ℝ))
          / Real.log (Real.log ((u n : ℝ) + 3))) atTop (𝓝 0) := by
  sorry

end Erdos249257.ExternalVerification243PaperStatementsD
