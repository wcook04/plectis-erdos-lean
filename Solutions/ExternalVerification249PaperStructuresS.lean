/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos249.FiniteDilationLinearIndependent
import ErdosProblems.Erdos249.FiniteDilationMixedModuli
import ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables
import ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadixClassification

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos249.FiniteDilationLinearIndependent`,
`ErdosProblems.Erdos249.FiniteDilationMixedModuli`,
`ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables`,
`ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadixClassification`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification249PaperStructuresS

noncomputable def positiveRadixValue (B : ℕ) (f : ℕ → ℚ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, (f (Nat.totient (n + 1) % m) : ℝ) / (B : ℝ) ^ (n + 1)

noncomputable def radixValue (B : ℕ) (a : ℕ → ℤ) : ℝ :=
  ∑' n : ℕ, (a n : ℝ) / (B : ℝ) ^ n

theorem linearIndependent_one_and_least_residue_values
    (m B : ℕ) (hm : 3 ≤ m) (hB : 2 ≤ B) :
    LinearIndependent ℚ (fun d : ℕ =>
      if d = 0 then (1 : ℝ) else
        positiveRadixValue (B ^ d) (fun r : ℕ => (r : ℚ)) m) := by
  first
  | (exact @ErdosProblems.Erdos249.FiniteDilationLinearIndependent.linearIndependent_one_and_least_residue_values m B hm hB; done)
  | (set_option smartUnfolding false in
      exact @ErdosProblems.Erdos249.FiniteDilationLinearIndependent.linearIndependent_one_and_least_residue_values m B hm hB; done)
  | (apply ErdosProblems.Erdos249.FiniteDilationLinearIndependent.linearIndependent_one_and_least_residue_values <;> assumption; done)
  | (simpa only [positiveRadixValue, radixValue] using ErdosProblems.Erdos249.FiniteDilationLinearIndependent.linearIndependent_one_and_least_residue_values; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @ErdosProblems.Erdos249.FiniteDilationLinearIndependent.linearIndependent_one_and_least_residue_values m B hm hB; done)
  | (with_unfolding_all exact @ErdosProblems.Erdos249.FiniteDilationLinearIndependent.linearIndependent_one_and_least_residue_values m B hm hB; done)

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
        f d (r : ZMod (2 ^ (k d))) = f d 0 := by
  first
  | (exact @ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff D k f B q₀ hB hpos hk; done)
  | (set_option smartUnfolding false in
      exact @ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff D k f B q₀ hB hpos hk; done)
  | (apply ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff <;> assumption; done)
  | (simpa only [positiveRadixValue, radixValue] using ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff D k f B q₀ hB hpos hk; done)
  | (with_unfolding_all exact @ErdosProblems.Erdos249.FiniteDilationMixedModuli.rational_mixed_moduli_with_constant_iff D k f B q₀ hB hpos hk; done)

theorem positiveRadixValue_eq_of_even_constant
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ℕ → ℚ) (c : ℚ)
    (hc : ∀ r, r < 2 ^ k → r % 2 = 0 → f r = c) :
    positiveRadixValue B f (2 ^ k) =
      ((B : ℝ) + 1) / (B : ℝ) ^ 2 * (f 1 : ℝ) +
        (c : ℝ) / ((B : ℝ) ^ 2 * ((B : ℝ) - 1)) := by
  first
  | (exact @ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables.positiveRadixValue_eq_of_even_constant B hB k hk f c hc; done)
  | (set_option smartUnfolding false in
      exact @ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables.positiveRadixValue_eq_of_even_constant B hB k hk f c hc; done)
  | (apply ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables.positiveRadixValue_eq_of_even_constant <;> assumption; done)
  | (simpa only [positiveRadixValue, radixValue] using ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables.positiveRadixValue_eq_of_even_constant; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables.positiveRadixValue_eq_of_even_constant B hB k hk f c hc; done)
  | (with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR7.IntegerRadixObservables.positiveRadixValue_eq_of_even_constant B hB k hk f c hc; done)

theorem radix_residue_series_irrational
    (B : ℕ) (hB : 2 ≤ B) {m : ℕ} (hm : 3 ≤ m) :
    Irrational (radixValue B (fun n => (Nat.totient n % m : ℤ))) := by
  first
  | (exact @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.radix_residue_series_irrational B hB m hm; done)
  | (set_option smartUnfolding false in
      exact @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.radix_residue_series_irrational B hB m hm; done)
  | (apply ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.radix_residue_series_irrational <;> assumption; done)
  | (simpa only [positiveRadixValue, radixValue] using ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.radix_residue_series_irrational; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.radix_residue_series_irrational B hB m hm; done)
  | (with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.radix_residue_series_irrational B hB m hm; done)

theorem rational_zmod_radix_observable_iff
    (B : ℕ) (hB : 2 ≤ B) {k : ℕ} (hk : 1 ≤ k)
    (f : ZMod (2 ^ k) → ℚ) :
    (∃ q : ℚ,
      (∑' n : ℕ, (f (Nat.totient (n + 1) : ZMod (2 ^ k)) : ℝ) /
        (B : ℝ) ^ (n + 1)) = (q : ℝ)) ↔
      ∀ r : ℕ, r < 2 ^ k → r % 2 = 0 → f (r : ZMod (2 ^ k)) = f 0 := by
  first
  | (exact @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.rational_zmod_radix_observable_iff B hB k hk f; done)
  | (set_option smartUnfolding false in
      exact @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.rational_zmod_radix_observable_iff B hB k hk f; done)
  | (apply ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.rational_zmod_radix_observable_iff <;> assumption; done)
  | (simpa only [positiveRadixValue, radixValue] using ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.rational_zmod_radix_observable_iff; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.rational_zmod_radix_observable_iff B hB k hk f; done)
  | (with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR7.RationalIntegerRadix.rational_zmod_radix_observable_iff B hB k hk f; done)

end Erdos249257.ExternalVerification249PaperStructuresS
