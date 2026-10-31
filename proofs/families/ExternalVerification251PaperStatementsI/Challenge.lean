/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #251

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos251.PaperCompleteR20.LocalTargetInterval`,
`ErdosProblems.Erdos251.SparseScheduleDensityR8`, `ErdosProblems.Erdos251.SparseScheduleR8`.
-/

open Filter
open Topology
open Finset

namespace Erdos249257.ExternalVerification251PaperStatementsI

noncomputable def gap (k : ℕ) : ℕ := (k + 4) ^ 2

noncomputable def amplitude (k : ℕ) : ℕ := 4 * (k + 3).factorial * 2 ^ gap k

noncomputable def Ready (f : ℕ → ℝ) (n k : ℕ) : Prop :=
  ∀ m, n ≤ m → (amplitude k : ℝ) ≤ f m ∧ amplitude k ≤ m + 1

noncomputable def UpperBanachZero (S : Set ℕ) : Prop := by
  classical
  exact ∀ R : ℕ, 0 < R → ∃ L₀ : ℕ, ∀ a L : ℕ, L₀ ≤ L →
    R * ((Finset.Ico a (a + L)).filter (fun n => n ∈ S)).card ≤ L

noncomputable def upgrade (f : ℕ → ℝ) (n k : ℕ) : ℕ := by
  classical
  exact if Ready f n (k + 1) then k + 1 else k

noncomputable def state (f : ℕ → ℝ) (start : ℕ) : ℕ → ℕ × ℕ
  | 0 => (start, 0)
  | j + 1 =>
      let s := state f start j
      let n := s.1 + gap s.2
      (n, upgrade f n s.2)

noncomputable def centre (f : ℕ → ℝ) (start j : ℕ) : ℕ := (state f start j).1

/-- States long251:res:local-targets from the long record for Erdős problem #251. Transported
from ErdosProblems.Erdos251.PaperCompleteR20.local_target_interval in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry

end Erdos249257.ExternalVerification251PaperStatementsI
