/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.PaperCompleteR7.RationalObservableClassification
import Solutions.PalomarCorpus.E249_30.Statement

open Filter Topology
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace PalomarCorpus.E249.RationalObservableClassification

theorem rational_zmod_observable_iff
    {k : ℕ} (hk : 1 ≤ k) (f : ZMod (2 ^ k) → ℚ) :
    (∃ q : ℚ,
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        2 ^ (n + 1)) = (q : ℝ)) ↔
      ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0 := by
  simpa only [totientResidueValue, ErdosProblems.Erdos249.totientResidueValue] using
    ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables.rational_zmod_observable_iff hk f

theorem zmod_observable_value
    {k : ℕ} (hk : 1 ≤ k) (f : ZMod (2 ^ k) → ℚ) (c : ℚ)
    (hc : ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = c) :
    (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
      2 ^ (n + 1)) = ((3 * f 1 / 4 + c / 4 : ℚ) : ℝ) := by
  simpa only [totientResidueValue, ErdosProblems.Erdos249.totientResidueValue] using
    ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables.zmod_observable_value hk f c hc

theorem residue_series_sharp_range :
    (∀ m : ℕ, 3 ≤ m → Irrational (totientResidueValue m)) ∧
    totientResidueValue 1 = 0 ∧ totientResidueValue 2 = 3 / 4 := by
  simpa only [totientResidueValue, ErdosProblems.Erdos249.totientResidueValue] using
    ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables.residue_series_sharp_range

theorem short_note_residue_theorem :
    (∀ m : ℕ, 3 ≤ m → Irrational (totientResidueValue m)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : ZMod (2 ^ k) → ℚ,
      ((∃ q : ℚ,
        (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
          2 ^ (n + 1)) = (q : ℝ)) ↔
        ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0)) ∧
    (∀ k : ℕ, 1 ≤ k → ∀ f : ZMod (2 ^ k) → ℚ, ∀ c : ℚ,
      (∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = c) →
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        2 ^ (n + 1)) = ((3 * f 1 / 4 + c / 4 : ℚ) : ℝ)) := by
  simpa only [totientResidueValue, ErdosProblems.Erdos249.totientResidueValue] using
    ErdosProblems.Erdos249.PaperCompleteR7.RationalObservables.short_note_residue_theorem

end PalomarCorpus.E249.RationalObservableClassification
end
