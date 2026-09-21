/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band f

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open Finset

namespace PalomarCorpus.E251.PaperStatementsF
open scoped BigOperators
open Finset
/-- Asymptotic density zero, with no assumption of existence of a density. Local copy of ErdosProblems.Erdos251.PaperR7.ZeroDensity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N
/-- Fixed-block polynomial nonconcentration for an integer word. Local copy of ErdosProblems.Erdos251.PaperR7.FixedBlockNonconcentration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}
/-- States long251:res:denominatorfloor from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.denominator_floor_decimal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem denominator_floor_decimal : (10 ^ 177 : ℕ) < 2 ^ 589 := by
  sorry
/-- States long251:res:nonconcentration from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.finite_perturbation_stability in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_perturbation_stability
    (a b : ℕ → ℤ) (E : Finset ℤ)
    (ha : FixedBlockNonconcentration a)
    (hE : ∀ n, b n - a n ∈ E) :
    FixedBlockNonconcentration b := by
  sorry
end PalomarCorpus.E251.PaperStatementsF
