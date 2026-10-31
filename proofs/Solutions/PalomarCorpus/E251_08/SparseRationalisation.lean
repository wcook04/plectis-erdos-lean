/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.SparsePaperR11
import Solutions.PalomarCorpus.E251_08.Statement

open Filter Topology Finset
open scoped BigOperators

namespace PalomarCorpus.E251.SparseRationalisation

private theorem state_eq_source (f : ℕ → ℝ) (start j : ℕ) :
    state f start j = ErdosProblems.Erdos251.PaperR8.SparseSchedule.state f start j := by
  induction j with
  | zero => rfl
  | succ j ih =>
      show ((state f start j).1 + gap (state f start j).2,
          upgrade f ((state f start j).1 + gap (state f start j).2) (state f start j).2) =
        ErdosProblems.Erdos251.PaperR8.SparseSchedule.state f start (j + 1)
      rw [ih] <;> rfl

private theorem centre_eq_source :
    centre = ErdosProblems.Erdos251.PaperR8.SparseSchedule.centre := by
  funext f start j
  exact congrArg Prod.fst (state_eq_source f start j)

theorem arbitrary_word_sparse_rationalisation (a : ℕ → ℕ) {A : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u : ℝ,
      S ⊆ Set.Ici K ∧ UpperBanachZero S ∧ A < l ∧ l < u ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
          q ∣ e n ∧ q ∣ ∑ i ∈ Finset.range n, e i) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  have hU : UpperBanachZero =
      ErdosProblems.Erdos251.PaperR8.SparseSchedule.UpperBanachZero := rfl
  rw [hU]
  exact ErdosProblems.Erdos251.PaperR9.SparseAmbient.arbitrary_word_sparse_rationalisation
    a ha f hf K

theorem polylogarithmic_word_interval (a : ℕ → ℕ) {A ε : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (hε : 0 < ε) (K : ℕ) :
    ∃ start : ℕ, ∃ l u C : ℝ,
      (Set.range (centre (polylog ε) start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre (polylog ε) start)) ∧
      A < l ∧ l < u ∧ 0 < C ∧
      (∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
        ((supportSlice (centre (polylog ε) start) X L).card : ℝ) ≤ C * X / iterlog X) ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre (polylog ε) start)) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
        (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
          q ∣ e n ∧ q ∣ ∑ i ∈ Finset.range n, e i) ∧
        (∀ n < K, a n + e n = a n) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r ∧
        ∀ m : ℕ → ℕ,
          Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0) →
          Tendsto (fun X => blockTV a (fun n => a n + e n) X (m X)) atTop (𝓝 0) ∧
          ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop,
            ∀ Φ : ℕ → (Fin (m X) → ℕ) → ℝ,
              (∀ N ∈ Finset.Ico X (2 * X), |Φ N (fun i => a (N + i.val))| ≤ 1) →
              (∀ N ∈ Finset.Ico X (2 * X), |Φ N (fun i => a (N + i.val) + e (N + i.val))| ≤ 1) →
              |testMean a X (m X) Φ - testMean (fun n => a n + e n) X (m X) Φ| < η := by
  have hU : UpperBanachZero =
      ErdosProblems.Erdos251.PaperR8.SparseSchedule.UpperBanachZero := rfl
  have hpolylog : polylog = ErdosProblems.Erdos251.PaperR11.SparsePolylog.polylog := rfl
  have hslice :
      supportSlice = ErdosProblems.Erdos251.PaperR8.SparseSchedule.supportSlice := rfl
  have hiterlog : iterlog = ErdosProblems.Erdos251.PaperR11.SparsePolylog.iterlog := rfl
  have hTV : (blockTV : (ℕ → ℕ) → (ℕ → ℕ) → ℕ → ℕ → ℝ) =
      ErdosProblems.Erdos251.PaperR11.GrowingBlocks.blockTV := rfl
  have hmean : (testMean : (ℕ → ℕ) → ℕ → (m : ℕ) → (ℕ → (Fin m → ℕ) → ℝ) → ℝ) =
      ErdosProblems.Erdos251.PaperR11.GrowingBlocks.testMean := rfl
  rw [hU, centre_eq_source, hpolylog, hslice, hiterlog, hTV, hmean]
  exact ErdosProblems.Erdos251.PaperR11.SparsePaper.polylogarithmic_word_interval a ha hε K

theorem growing_block_TV {α : Type*} (a b : ℕ → α) {β : ℝ}
    (hβ : 0 < β) (start : ℕ)
    (hchange : ∀ n, a n ≠ b n → n ∈ Set.range (centre (polylog β) start))
    (m : ℕ → ℕ) (hm : Tendsto (fun X => (m X : ℝ) / iterlog X) atTop (𝓝 0)) :
    Tendsto (fun X => blockTV a b X (m X)) atTop (𝓝 0) := by
  have hpolylog : polylog = ErdosProblems.Erdos251.PaperR11.SparsePolylog.polylog := rfl
  have hiterlog : iterlog = ErdosProblems.Erdos251.PaperR11.SparsePolylog.iterlog := rfl
  have hTV : (blockTV : (ℕ → α) → (ℕ → α) → ℕ → ℕ → ℝ) =
      ErdosProblems.Erdos251.PaperR11.GrowingBlocks.blockTV := rfl
  rw [centre_eq_source, hpolylog] at hchange
  rw [hiterlog] at hm
  rw [hTV]
  exact ErdosProblems.Erdos251.PaperR11.GrowingBlocks.growing_block_TV a b hβ start hchange m hm

end PalomarCorpus.E251.SparseRationalisation
