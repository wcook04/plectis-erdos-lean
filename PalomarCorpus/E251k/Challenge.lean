/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band k

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology
open Finset
open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsK
open Filter
open Topology
open Finset
open scoped BigOperators
/-- Asymptotic density zero, with no assumption of existence of a density. Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.ZeroDensity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N
/-- Fixed-block polynomial nonconcentration for an integer word. Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.FixedBlockNonconcentration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}
/-- States long251:res:sparse-nonconcentration from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.sparse_nonconcentration in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sparse_nonconcentration (a b : ℕ → ℤ) (S : Set ℕ)
    (hS : ZeroDensity S) (hab : ∀ n, n ∉ S → a n = b n)
    (ha : FixedBlockNonconcentration a) : FixedBlockNonconcentration b := by
  sorry
end PalomarCorpus.E251.PaperStatementsK
