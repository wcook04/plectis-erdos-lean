/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.SparsePaperR11
import ErdosProblems.Erdos251.SparseAmbientR9
import Solutions.PalomarCorpus.E251.Statement

open Filter Topology
open scoped BigOperators
open Finset

set_option autoImplicit false
noncomputable section
namespace PalomarCorpus.E251.UniformSparseRationalisation
export PalomarCorpus.E251.Shared (UpperBanachZero eventStarts iterlog polylog)

theorem polylogarithmic_word_interval_uniform (a : ℕ → ℕ) {A ε : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (hε : 0 < ε) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u C : ℝ, ∃ Nq : ℕ → ℕ,
      (S ⊆ Set.Ici K) ∧
      UpperBanachZero (S) ∧
      A < l ∧ l < u ∧ 0 < C ∧
      (∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
        ((supportSlice S X L).card : ℝ) ≤ C * X / iterlog X) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop,
          ∀ b : ℕ → ℕ,
            (∀ n, a n ≠ b n → n ∈ S) →
            blockTV a b X (m X) < η) ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        (∀ n < K, a n + e n = a n) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r ∧
        ∀ X m : ℕ, blockTV a (fun n => a n + e n) X m ≤
          (m : ℝ) * (supportSlice S X (X + m)).card / X := by
  obtain ⟨start, h⟩ :=
    ErdosProblems.Erdos251.PaperR11.SparsePaper.polylogarithmic_word_interval_uniform a ha hε K
  refine ⟨Set.range (ErdosProblems.Erdos251.PaperR8.SparseSchedule.centre
    (ErdosProblems.Erdos251.PaperR11.SparsePolylog.polylog ε) start), ?_⟩
  simpa only [eventStarts, ErdosProblems.Erdos251.PaperR7.eventStarts, eventFrequency, blockTV, ErdosProblems.Erdos251.PaperR11.GrowingBlocks.eventFrequency, ErdosProblems.Erdos251.PaperR11.GrowingBlocks.blockTV, UpperBanachZero, ErdosProblems.Erdos251.PaperR8.SparseSchedule.UpperBanachZero, polylog, iterlog, ErdosProblems.Erdos251.PaperR11.SparsePolylog.polylog, ErdosProblems.Erdos251.PaperR11.SparsePolylog.iterlog, supportSlice, ErdosProblems.Erdos251.PaperR8.SparseSchedule.supportSlice] using h

theorem arbitrary_word_sparse_rationalisation_uniform (a : ℕ → ℕ) {A : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u : ℝ, ∃ Nq : ℕ → ℕ,
      S ⊆ Set.Ici K ∧ UpperBanachZero S ∧ A < l ∧ l < u ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  simpa only [UpperBanachZero, ErdosProblems.Erdos251.PaperR8.SparseSchedule.UpperBanachZero] using
    ErdosProblems.Erdos251.PaperR9.SparseAmbient.arbitrary_word_sparse_rationalisation_uniform a ha f hf K

end PalomarCorpus.E251.UniformSparseRationalisation
end
