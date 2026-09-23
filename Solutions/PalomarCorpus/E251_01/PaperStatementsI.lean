/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperCompleteR20.LocalTargetInterval
import ErdosProblems.Erdos251.SparseScheduleDensityR8
import ErdosProblems.Erdos251.SparseScheduleR8
import Solutions.PalomarCorpus.E251_01.Statement

open Filter
open Topology
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsI
export PalomarCorpus.E251_01.Shared (UpperBanachZero)

theorem local_target_interval (a : ℕ → ℕ) {A η : ℝ}
    (ha : HasSum (fun n => (a n : ℝ)/2^(n+1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) (hη : 0 < η) :
    ∃ start : ℕ, ∃ l u : ℝ, ∃ Nq : ℕ → ℕ,
      (Set.range (centre f start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre f start)) ∧
      A < l ∧ l < u ∧ u < A+η ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre f start)) ∧
        (∀ n < K, a n+e n = a n) ∧
        (∀ᶠ n in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        HasSum (fun n => ((a n+e n : ℕ) : ℝ)/2^(n+1)) r := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos251.PaperCompleteR20.local_target_interval a A η ha f hf K hη

end PalomarCorpus.E251.PaperStatementsI
