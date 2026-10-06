/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.FiniteDilationLinearIndependent
import ErdosProblems.Erdos249.FiniteDilationMixedModuli
import ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables
import ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadixClassification
import Solutions.PalomarCorpus.E249_33.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStructuresS

theorem linearIndependent_one_and_least_residue_values
    (m B : ℕ) (hm : 3 ≤ m) (hB : 2 ≤ B) :
    LinearIndependent ℚ (fun d : ℕ =>
      if d = 0 then (1 : ℝ) else
        positiveRadixValue (B ^ d) (fun r : ℕ => (r : ℚ)) m) := @ErdosProblems.Erdos249.FiniteDilationLinearIndependent.linearIndependent_one_and_least_residue_values m B hm hB

theorem rational_mixed_moduli_with_constant_iff
    (D : Finset ℕ) (k : ℕ → ℕ)
    (f : (d : ℕ) → ZMod (2 ^ (k d)) → ℚ) (B : ℕ) (q₀ : ℚ)
    (hB : 2 ≤ B)
    (hpos : ∀ d ∈ D, 0 < d)
    (hk : ∀ d ∈ D, 0 < k d) :
    (∃ q : ℚ, (q₀ : ℝ) + (∑ d ∈ D, ∑' n : ℕ,
      (f d (Nat.totient (n + 1) : ZMod (2 ^ (k d))) : ℝ) /
        ((B : ℝ) ^ d) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ d ∈ D, ∀ r : ℕ, r < 2 ^ (k d) → Even r →
        f d (r : ZMod (2 ^ (k d))) = f d 0 := @ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff D k f B q₀ hB hpos hk

theorem positiveRadixValue_eq_of_even_constant
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ℕ → ℚ) (c : ℚ)
    (hc : ∀ r, r < 2 ^ k → r % 2 = 0 → f r = c) :
    positiveRadixValue B f (2 ^ k) =
      ((B : ℝ) + 1) / (B : ℝ) ^ 2 * (f 1 : ℝ) +
        (c : ℝ) / ((B : ℝ) ^ 2 * ((B : ℝ) - 1)) := @ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables.positiveRadixValue_eq_of_even_constant B hB k hk f c hc

theorem radix_residue_series_irrational
    (B : ℕ) (hB : 2 ≤ B) {m : ℕ} (hm : 3 ≤ m) :
    Irrational (radixValue B (fun n => (Nat.totient n % m : ℤ))) := @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.radix_residue_series_irrational B hB m hm

theorem rational_zmod_radix_observable_iff
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ZMod (2 ^ k) → ℚ) :
    (∃ q : ℚ,
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        (B : ℝ) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0 := @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.rational_zmod_radix_observable_iff B hB k hk f

end PalomarCorpus.E249.PaperStructuresS
