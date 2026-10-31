/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `6917e15ec4abc2623512254da93221e446eeb707` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.Counterexample.Defs`,
`ErdosProblems.Erdos1041.Counterexample.HausdorffLength`.
-/

open scoped ENNReal
open MeasureTheory
open Polynomial
open Metric
open scoped ComplexConjugate

namespace Erdos249257.ExternalVerification1041PaperStatementsAE

noncomputable def s : ℚ := 1 / 10 ^ 6

noncomputable def fcLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s

/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from
the long record and the short record for Erdős problem #1041. Transported from
Erdos1041.Counterexample.erdos1041_hausdorff_answer_false in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_hausdorff_answer_false :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2 := by
  sorry

/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from
the long record and the short record for Erdős problem #1041. Transported from
Erdos1041.Counterexample.erdos1041_hausdorff_negation in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_hausdorff_negation :
    ¬ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2 := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsAE
