/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.AllResidueLogarithmicR9
import Solutions.PalomarCorpus.E251.Statement

open Filter
open scoped BigOperators Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.AllResidueLogarithmicCountermodel

theorem exists_every_residue_logarithmic_countermodel :
    ∃ digit carry position : ℕ → ℤ,
    (∀ n, position n = 3 + ∑ j ∈ Finset.range n, digit (j + 1)) ∧
    (∀ n, 1 ≤ n → 0 < digit n ∧ (2 : ℤ) ∣ digit n) ∧
    (∀ t r : ℕ, 0 < t → r < t → ∀ N : ℕ,
      ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ i % t = r ∧ j % t = r ∧ digit i = 2 ∧ digit j = 4) ∧
    (∀ B₀ : ℤ, ∀ N : ℕ, ∃ n, N ≤ n ∧ B₀ < digit n) ∧
    (∀ h : ℕ, 0 < h → ¬ ∃ N₀, ∀ n, N₀ ≤ n → digit (n + h) = digit n) ∧
    (∀ n : ℕ, (digit n : ℝ) ≤ 4 * Real.log ((n : ℝ) + 1) + 24) ∧
    StrictMono position ∧ (∀ n, ∃ z : ℤ, position n = 2 * z + 1) ∧
    HasSum (fun j : ℕ => (digit (j + 1) : ℝ) / 2 ^ (j + 1)) 6 ∧
    (∀ N : ℕ, HasSum (fun j : ℕ => (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (carry N : ℝ)) ∧
    (∀ N h : ℕ, ∃ z : ℤ,
      (∑' j : ℕ, (digit (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
      (∑' j : ℕ, (digit (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z) ∧
    Tendsto (fun N : ℕ => (position N : ℝ) / ((N : ℝ) * Real.log N)) atTop (𝓝 1) := by
  refine ⟨ErdosProblems.Erdos251.PaperR9.AllResidueLog.digit, ErdosProblems.Erdos251.PaperR9.AllResidueLog.carry, ErdosProblems.Erdos251.PaperR9.AllResidueLog.position, ?_,
    ErdosProblems.Erdos251.PaperR9.AllResidueLog.every_residue_countermodel⟩
  intro n
  rfl

end PalomarCorpus.E251.AllResidueLogarithmicCountermodel
