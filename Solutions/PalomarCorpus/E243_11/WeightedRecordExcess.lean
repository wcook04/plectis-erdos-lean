/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR8.GrowthDebtSummability
import Solutions.PalomarCorpus.E243_11.Statement

open Filter
open scoped Topology

namespace PalomarCorpus.E243.WeightedRecordExcess
noncomputable section

theorem weighted_record_excess (a : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)^2) atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop) :
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
      ∃ B : ℕ, Summable (weight a p q B f) := by
  classical
  have hL : ∀ n, L q a n = ErdosProblems.Erdos243.cumulativeDigitLcm q a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [L, ErdosProblems.Erdos243.cumulativeDigitLcm, ih]
  have hM : ∀ n, M q a n = ErdosProblems.Erdos243.cumulativeOverlapDebt q a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [M, ErdosProblems.Erdos243.cumulativeOverlapDebt, ih, hL]
  have h := ErdosProblems.Erdos243.PaperCompleteR8.canonical_weighted_record
    a ha hapos p q hq hs hg f hf hpos hdiv
  change (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
    ∃ B : ℕ, Summable (fun n : ℕ =>
      if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
        (((-V a p q n - B).toNat : ℕ) : ℝ) * f (U a p q n) else 0)
  simpa only [U, V, C, hM, hL,
    ErdosProblems.Erdos243.PaperCompleteR8.canonicalLcmOrbit,
    ErdosProblems.Erdos243.PaperCompleteR8.Record,
    ErdosProblems.Erdos243.lcmLiftedNumerator,
    ErdosProblems.Erdos243.lcmLiftedDigit,
    ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator,
    ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator,
    ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct,
    ErdosProblems.Erdos243.sylvesterNext] using h

theorem weighted_growth_record_excess (a : ℕ → ℕ) (ha : StrictMono a)
    (hapos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hg : Tendsto (fun n => (a (n+1) : ℝ) / (a n : ℝ)^2) atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x)
    (hdiv : Tendsto (fun x : ℝ => ∫ t in (1 : ℝ)..x, f t) atTop atTop) :
    (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
      ∃ B : ℕ, Summable (growthWeight a p q B f) := by
  classical
  have hL : ∀ n, L q a n = ErdosProblems.Erdos243.cumulativeDigitLcm q a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [L, ErdosProblems.Erdos243.cumulativeDigitLcm, ih]
  have hM : ∀ n, M q a n = ErdosProblems.Erdos243.cumulativeOverlapDebt q a n := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => simp only [M, ErdosProblems.Erdos243.cumulativeOverlapDebt, ih, hL]
  have h := ErdosProblems.Erdos243.PaperCompleteR8.canonical_weighted_growth_record_factored
    a ha hapos p q hq hs hg f hf hpos hdiv
  change (∃ N, ∀ n, N ≤ n → (a (n+1) : ℤ) = (a n : ℤ)^2 - a n + 1) ↔
    ∃ B : ℕ, Summable (fun n : ℕ =>
      if (∀ j ≤ n, U a p q j < U a p q (n+1)) then
        (U a p q n : ℝ) * f (U a p q n) *
          max ((a n : ℝ)^2 / (a (n+1) : ℝ) - 1 - (B : ℝ) / U a p q n) 0
      else 0)
  simpa only [U, V, C, hM, hL,
    ErdosProblems.Erdos243.PaperCompleteR8.canonicalLcmOrbit,
    ErdosProblems.Erdos243.PaperCompleteR8.Record,
    ErdosProblems.Erdos243.lcmLiftedNumerator,
    ErdosProblems.Erdos243.lcmLiftedDigit,
    ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator,
    ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator,
    ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct,
    ErdosProblems.Erdos243.sylvesterNext] using h

end
end PalomarCorpus.E243.WeightedRecordExcess
