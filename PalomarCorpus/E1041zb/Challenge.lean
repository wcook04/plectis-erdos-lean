/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band b

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Set
open MeasureTheory
open Polynomial
open scoped ComplexConjugate
open scoped BigOperators

namespace PalomarCorpus.E1041.PaperStatementsZB
open Set
open MeasureTheory
open Polynomial
open scoped ComplexConjugate
open scoped BigOperators
/-- A closed sublevel connector, allowing the zero-length repeated-root case. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ConnectedAtMost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedAtMost (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ ≤ R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.CriticalMinimum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalMinimum (p : ℂ[X]) (μ : ℝ) : Prop :=
  IsLeast {x : ℝ | ∃ c : ℂ, p.derivative.eval c = 0 ∧ x = ‖p.eval c‖} μ
/-- The Jordan-domain half-perimeter property of a component `U` of a closed sublevel set: any interior point is joined to any boundary point, inside the sublevel set `{|f| ≤ R}`, by a rectifiable path of length at most half of `H¹(∂U)`. The paper calls this elementary; its proof selects one of the two boundary arcs of a Jordan curve, which needs the Jordan curve theorem. Mathlib v4.29.1 has no Jordan curve theorem. `connectedAtMost_half_perimeter` below derives this property from the arc datum the Jordan curve supplies, so the only external part is the existence of that datum. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.HalfPerimeterJoin, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfPerimeterJoin (f : ℂ → ℂ) (R : ℝ) (U : Set ℂ) : Prop :=
  ∀ H : ℝ, μH[(1 : ℝ)] (frontier U) ≤ ENNReal.ofReal H →
    ∀ p ∈ U, ∀ q ∈ frontier U, ConnectedAtMost f R (H / 2) p q
/-- The paper's conclusion: two distinct roots joined inside `{|f| ≤ R}` by a rectifiable path of length at most `L`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.HasDistinctConnectionAtMost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasDistinctConnectionAtMost (f : ℂ → ℂ) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ f a = 0 ∧ f b = 0 ∧ ConnectedAtMost f R L a b
/-- The classical input of stage 1: at the first critical level the sublevel set carries two distinct one-root components `U_a`, `U_b` whose closures meet at a critical point, each of perimeter at most `P`, and each with the half-perimeter joining property. This packages exactly the theorems Mathlib does not carry: the component-wise Riemann–Hurwitz count of `eks2010` Proposition 2.1, the continuous extension of the inverse branch through `f(z) - f(c) = (z-c)^d h(z)`, lower semicontinuity of length under uniform convergence, and the Jordan curve theorem behind `HalfPerimeterJoin`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.SubcriticalSplitExists, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SubcriticalSplitExists (f : ℂ → ℂ) (μ P : ℝ) : Prop :=
  ∃ (a b c : ℂ) (Ua Ub : Set ℂ), a ≠ b ∧ f a = 0 ∧ f b = 0 ∧
    a ∈ Ua ∧ b ∈ Ub ∧ c ∈ frontier Ua ∧ c ∈ frontier Ub ∧
    μH[(1 : ℝ)] (frontier Ua) ≤ ENNReal.ofReal P ∧
    μH[(1 : ℝ)] (frontier Ub) ≤ ENNReal.ofReal P ∧
    HalfPerimeterJoin f μ Ua ∧ HalfPerimeterJoin f μ Ub
/-- States res:conjecture-p-consumer from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.subcritical_perimeter_path_paper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem subcritical_perimeter_path_paper
    (p : Polynomial ℂ) (n : ℕ) (μ β : ℝ)
    (hmonic : p.Monic) (hsf : Squarefree p) (hdeg : p.natDegree = n) (hn : 2 ≤ n)
    (hμ : CriticalMinimum p μ) (hμpos : 0 < μ) (hβ : 0 < β)
    (hperim : ∀ σ : ℝ, 0 < σ → σ < μ → ∀ z : ℂ, ‖p.eval z‖ ≤ σ →
      μH[(1 : ℝ)] (frontier (connectedComponentIn {w : ℂ | ‖p.eval w‖ ≤ σ} z))
        ≤ ENNReal.ofReal (β * σ ^ (1 / (n : ℝ))))
    (hsplit : SubcriticalSplitExists (fun z => p.eval z) μ (β * μ ^ (1 / (n : ℝ)))) :
    HasDistinctConnectionAtMost (fun z => p.eval z) μ (β * μ ^ (1 / (n : ℝ))) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsZB
