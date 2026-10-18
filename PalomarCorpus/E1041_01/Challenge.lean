/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1041, record sections 1 to 2: the historical question; trinomials

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1041, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. A degree-seven counterexample due to ani,
formalised in this corpus, refutes the total-variation formulation of Erdős problem
#1041; the theorems in this entry keep their stated hypotheses.
-/

open scoped ENNReal
open Polynomial
open Metric
open MeasureTheory
open scoped ComplexConjugate
open Set
open scoped NNReal

namespace PalomarCorpus.E1041_01.Shared
/-- Local definition s, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def s : ℚ := 1 / 10 ^ 6
/-- Local definition t, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def t : ℚ := 417 / 40
/-- Local definition A, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def A : ℚ := -5 + 12 * t - 3 * t ^ 2
/-- Local definition B, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def B : ℚ := -4 + 4 * t + 6 * t ^ 2
/-- Local definition Cconst, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def Cconst : ℚ := t * (-8 + 15 * t - 2 * t ^ 2)
/-- Local definition a, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def a : ℂ := (A : ℂ) - (s : ℂ) * Complex.I
/-- Local definition b, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def b : ℂ := Complex.I * (B : ℂ) + (9 / 5 : ℚ) * (s : ℂ)
/-- Local definition c, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def c : ℂ := -(Cconst : ℂ) - (162 / 25 : ℚ) * (s : ℂ) * Complex.I
noncomputable def ε : ℚ := s ^ 2
noncomputable def ρ : ℚ := 1 - s ^ 16
/-- Local definition f, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def f : Polynomial ℂ :=
  Polynomial.X ^ 7
    + Polynomial.C (-(ρ : ℂ) * (ε : ℂ) ^ 6 * conj c) * Polynomial.X ^ 6
    + Polynomial.C (-(ρ : ℂ) ^ 2 * (ε : ℂ) ^ 5 * conj b) * Polynomial.X ^ 5
    + Polynomial.C (-(ρ : ℂ) ^ 3 * (ε : ℂ) ^ 4 * conj a) * Polynomial.X ^ 4
    + Polynomial.C ((ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * a) * Polynomial.X ^ 3
    + Polynomial.C ((ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5 * b) * Polynomial.X ^ 2
    + Polynomial.C ((ρ : ℂ) ^ 6 * (ε : ℂ) ^ 6 * c) * Polynomial.X
    + Polynomial.C (-(ρ : ℂ) ^ 7)
/-- A public function spelling exactly the trinomial in both papers. Local copy of ErdosProblems.Erdos1041.PaperTrinomial.polynomialValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialValue (n m : ℕ) (a b z : ℂ) : ℂ := z ^ n + a * z ^ m + b
end PalomarCorpus.E1041_01.Shared

namespace PalomarCorpus.E1041.PaperStatementsA
open scoped ENNReal
open Polynomial
open Metric
/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from the long record and the short record for Erdős problem #1041. Transported from Erdos1041.Counterexample.erdos1041_ani_degree_seven in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_ani_degree_seven :
    ∃ (p : ℂ[X]), p.Monic ∧ p.natDegree = 7 ∧
      (∀ z, p.IsRoot z → ‖z‖ < 1) ∧ p.roots.Nodup ∧
      ∀ z₁ z₂, p.IsRoot z₁ → p.IsRoot z₂ → z₁ ≠ z₂ →
        ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) →
          γ 0 = z₁ → γ 1 = z₂ →
          (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖p.eval (γ τ)‖ < 1) →
          (2 : ℝ≥0∞) < eVariationOn γ (Set.Icc 0 1) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsA

namespace PalomarCorpus.E1041.PaperStatementsAE
open scoped ENNReal
open MeasureTheory
open Polynomial
open Metric
open scoped ComplexConjugate
export PalomarCorpus.E1041_01.Shared (s)
/-- Local definition fcLength, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def fcLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s
/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from the long record and the short record for Erdős problem #1041. Transported from Erdos1041.Counterexample.erdos1041_hausdorff_answer_false in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_hausdorff_answer_false :
    False ↔ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2 := by
  sorry
/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from the long record and the short record for Erdős problem #1041. Transported from Erdos1041.Counterexample.erdos1041_hausdorff_negation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_hausdorff_negation :
    ¬ ∀ (n : ℕ) (f : ℂ[X]), n ≥ 2 → f.natDegree = n → f.Monic →
      f.rootSet ℂ ⊆ Metric.ball 0 1 →
      ∃ (z₁ z₂ : ℂ) (h : ({z₁, z₂} : Multiset ℂ) ≤ f.roots) (γ : Path z₁ z₂),
        Set.range γ ⊆ { z : ℂ | ‖f.eval z‖ < 1 } ∧ fcLength (Set.range γ) < 2 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsAE

namespace PalomarCorpus.E1041.PaperStructuresAF
open scoped ComplexConjugate
open scoped ENNReal
export PalomarCorpus.E1041_01.Shared (A B Cconst a b c f s t)
/-- Local definition pathLength, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pathLength (γ : ℝ → ℂ) : ENNReal := eVariationOn γ (Set.Icc 0 1)
/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from the long record and the short record for Erdős problem #1041. Transported from Erdos1041.Counterexample.erdos1041_counterexample in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_counterexample :
    f.Monic ∧ f.natDegree = 7 ∧
    (∀ z, f.IsRoot z → ‖z‖ < 1) ∧
    f.roots.Nodup ∧
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc 0 1) → γ 0 = z₁ → γ 1 = z₂ →
        (∀ τ ∈ Set.Icc (0 : ℝ) 1, ‖f.eval (γ τ)‖ < 1) →
        (2 : ENNReal) < pathLength γ := by
  sorry
end PalomarCorpus.E1041.PaperStructuresAF

namespace PalomarCorpus.E1041.PaperStructuresAG
open scoped ENNReal
open MeasureTheory
open Polynomial
open Metric
open scoped ComplexConjugate
export PalomarCorpus.E1041_01.Shared (A B Cconst a b c f s t)
/-- Local definition Omega, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def Omega (p : Polynomial ℂ) : Set ℂ := {z : ℂ | ‖p.eval z‖ < 1}
/-- States res:ani-degree-seven-counterexample, res:ani-degree-seven-counterexample-long from the long record and the short record for Erdős problem #1041. Transported from Erdos1041.Counterexample.erdos1041_counterexample_hausdorff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdos1041_counterexample_hausdorff :
    ∀ z₁ z₂, f.IsRoot z₁ → f.IsRoot z₂ → z₁ ≠ z₂ →
      ∀ K : Set ℂ, IsPreconnected K → z₁ ∈ K → z₂ ∈ K → K ⊆ Omega f →
        (2 : ℝ≥0∞) < μH[1] K := by
  sorry
end PalomarCorpus.E1041.PaperStructuresAG

namespace PalomarCorpus.E1041.PaperStatementsAA
open Set
open scoped NNReal
open scoped ENNReal
export PalomarCorpus.E1041_01.Shared (polynomialValue)
/-- A continuous broken line `a → h → b`, with no division by a segment length. Local copy of ErdosProblems.Erdos1041.PaperCurve.hub, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hub (a h b : ℂ) (t : ℝ) : ℂ :=
  h + ((max (1 - t) 0 : ℝ) : ℂ) * (a - h) + ((max (t - 1) 0 : ℝ) : ℂ) * (b - h)
/-- States res:trinomial-all-degree from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperTrinomial.complete_trinomial in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem complete_trinomial {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z₁ z₂ : ℂ} (h₁ : polynomialValue n m a b z₁ = 0)
    (h₂ : polynomialValue n m a b z₂ = 0) :
    Continuous (hub z₁ 0 z₂) ∧
    hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
    (∀ t ∈ Icc (0 : ℝ) 2,
      ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
    BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal = ‖z₁‖ + ‖z₂‖ ∧
    (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2 := by
  sorry
/-- States res:trinomial-all-degree from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperTrinomialWholeR21.all_degree_monic_trinomials_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem all_degree_monic_trinomials_whole
    {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1) :
    (∀ z : ℂ, polynomialValue n m a b z = 0 →
      ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
        ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1) ∧
    ∀ z₁ z₂ : ℂ,
      polynomialValue n m a b z₁ = 0 →
      polynomialValue n m a b z₂ = 0 → z₁ ≠ z₂ →
      Continuous (hub z₁ 0 z₂) ∧
      hub z₁ 0 z₂ 0 = z₁ ∧ hub z₁ 0 z₂ 2 = z₂ ∧
      (∀ t ∈ Icc (0 : ℝ) 2,
        ‖polynomialValue n m a b (hub z₁ 0 z₂ t)‖ < 1) ∧
      BoundedVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2) ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal =
        ‖z₁‖ + ‖z₂‖ ∧
      (eVariationOn (hub z₁ 0 z₂) (Icc (0 : ℝ) 2)).toReal < 2 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsAA

namespace PalomarCorpus.E1041.PaperStatementsH
open Set
export PalomarCorpus.E1041_01.Shared (polynomialValue)
/-- States res:trinomial-all-degree from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperTrinomial.all_spokes in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem all_spokes {n m : ℕ} (hm : 1 ≤ m) (hmn : m < n) {a b : ℂ}
    (hroots : ∀ z : ℂ, polynomialValue n m a b z = 0 → ‖z‖ < 1)
    {z : ℂ} (hz : polynomialValue n m a b z = 0)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ‖polynomialValue n m a b ((t : ℂ) * z)‖ < 1 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsH
