/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.Counterexample.Assembly`,
`ErdosProblems.Erdos1041.Counterexample.Defs`.
-/

open scoped ComplexConjugate
open scoped ENNReal

namespace Erdos249257.ExternalVerification1041PaperStructuresAF

noncomputable def t : ℚ := 417 / 40

noncomputable def A : ℚ := -5 + 12 * t - 3 * t ^ 2

noncomputable def B : ℚ := -4 + 4 * t + 6 * t ^ 2

noncomputable def Cconst : ℚ := t * (-8 + 15 * t - 2 * t ^ 2)

noncomputable def s : ℚ := 1 / 10 ^ 6

noncomputable def a : ℂ := (A : ℂ) - (s : ℂ) * Complex.I

noncomputable def b : ℂ := Complex.I * (B : ℂ) + (9 / 5 : ℚ) * (s : ℂ)

noncomputable def c : ℂ := -(Cconst : ℂ) - (162 / 25 : ℚ) * (s : ℂ) * Complex.I

noncomputable def f : Polynomial ℂ :=
  Polynomial.X ^ 7
    + Polynomial.C (-(ρ : ℂ) * (ε : ℂ) ^ 6 * conj c) * Polynomial.X ^ 6
    + Polynomial.C (-(ρ : ℂ) ^ 2 * (ε : ℂ) ^ 5 * conj b) * Polynomial.X ^ 5
    + Polynomial.C (-(ρ : ℂ) ^ 3 * (ε : ℂ) ^ 4 * conj a) * Polynomial.X ^ 4
    + Polynomial.C ((ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * a) * Polynomial.X ^ 3
    + Polynomial.C ((ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5 * b) * Polynomial.X ^ 2
    + Polynomial.C ((ρ : ℂ) ^ 6 * (ε : ℂ) ^ 6 * c) * Polynomial.X
    + Polynomial.C (-(ρ : ℂ) ^ 7)

noncomputable def pathLength (γ : ℝ → ℂ) : ENNReal := eVariationOn γ (Set.Icc 0 1)

/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from
the long record and the short record for Erdős problem #1041. Transported from
Erdos1041.Counterexample.erdos1041_counterexample in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_counterexample :
    f.Monic ∧ f.natDegree = 7 ∧
    (∀ z, f.IsRoot z → ‖z‖ < 1) ∧
    f.roots.Nodup ∧
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) → γ 0 = z₁ → γ 1 = z₂ →
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖f.eval (γ τ)‖ < 1) →
        (2 : ENNReal) < pathLength γ := by
  sorry

end Erdos249257.ExternalVerification1041PaperStructuresAF
