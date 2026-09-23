/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1041, record sections 4 to 7; the cubic path family: a path estimate from area and boundary length; degree three; collinear roots and two sparse polynomial families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1041, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. A degree-seven counterexample due to ani,
formalised in this corpus, refutes the total-variation formulation of Erdős problem
#1041; the theorems in this entry keep their stated hypotheses.
-/

open Polynomial
open Set
open scoped ComplexConjugate
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
open MeasureTheory
open Finset
open Polynomial Set
open Polynomial Metric

namespace PalomarCorpus.E1041_02.Shared
/-- A closed sublevel connector, allowing the zero-length repeated-root case. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ConnectedAtMost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedAtMost (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ ≤ R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.CriticalMinimum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalMinimum (p : ℂ[X]) (μ : ℝ) : Prop :=
  IsLeast {x : ℝ | ∃ c : ℂ, p.derivative.eval c = 0 ∧ x = ‖p.eval c‖} μ
/-- Two zero occurrences joined by a path of length at most `L` inside the OPEN sublevel set `{|f| < R}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaJoinedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
end PalomarCorpus.E1041_02.Shared

namespace PalomarCorpus.E1041.PaperStatementsZA
open Polynomial
open Set
open scoped ComplexConjugate
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
export PalomarCorpus.E1041_02.Shared (ConnectedAtMost CriticalMinimum cfaJoinedBelow)
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.RootEnumeration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RootEnumeration {n : ℕ} (p : ℂ[X]) (z : Fin n → ℂ) : Prop :=
  p = ∏ i, (X - C (z i))
/-- The arity corollary's bracket: the (CF) bracket after the reductions `ρ ≤ 1` and `(λμ)^{1/n} ≤ 1` that its proof performs. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaArityBracket, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaArityBracket (lam r : ℝ) : ℝ :=
  Real.sqrt 2 * r / (1 - r) ^ 2 + Real.sqrt (Real.log (lam / r)) +
    Real.pi / Real.sqrt (Real.log lam)
/-- **External input for `res:constant-factor-arity`.** The same construction as `CFAPathConstruction`, in the shape its corollary's proof uses: every selected component contains the first-merge component, so its root count is at least `k₀`, and the reductions `ρ ≤ 1`, `(λμ)^{1/n} ≤ 1` available when `λμ ≤ 1` have already been made. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.CFAArityConstruction, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CFAArityConstruction (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (k₀ : ℕ) (lam r : ℝ) : Prop :=
  cfaJoinedBelow f z 1 (Real.sqrt (2 / (k₀ : ℝ)) * cfaArityBracket lam r)
/-- The paper's displayed bracket (CF). Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaBracket, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaBracket (n k : ℕ) (lam r : ℝ) : ℝ :=
  Real.sqrt (2 / (k : ℝ)) *
    (Real.sqrt 2 * r / (1 - r) ^ 2 +
      lam ^ ((1 : ℝ) / (n : ℝ)) *
        (Real.sqrt (Real.log (lam / r)) + Real.pi / Real.sqrt (Real.log lam)))
/-- External input for `res:constant-factor-path`, the paper's construction: for a monic `f` of degree `n ≥ 3` with least critical modulus `μ > 0`, every `r ∈ (0,1)` and `λ > 1` give a selected component with `k ≥ 2` roots and a path in `{|f| < λμ}` between two zero occurrences of length at most the bracket (CF) times `μ^{1/n}`. The proof uses Pólya's area inequality, the Koebe distortion theorem, the coarea formula, the area formula for the univalent inverse branches and a mean-value choice of a regular level strictly inside its window. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.CFAPathConstruction, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CFAPathConstruction : Prop :=
  ∀ (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (μ lam r : ℝ),
    3 ≤ n → f.Monic → f.natDegree = n → RootEnumeration f z →
    CriticalMinimum f μ → 0 < μ → 0 < r → r < 1 → 1 < lam →
    ∃ k : ℕ, 2 ≤ k ∧
      cfaJoinedBelow f z (lam * μ) (cfaBracket n k lam r * μ ^ ((1 : ℝ) / (n : ℝ)))
/-- Two zero occurrences joined by a path of length at most `L` inside the closed sublevel set `{|f| ≤ R}`, with distinct locations when `f` is squarefree. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaJoinedAtMost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaJoinedAtMost {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ ConnectedAtMost f.eval R L (z i) (z j) ∧
    (Squarefree f → z i ≠ z j)
/-- States res:constant-factor-arity from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.cfa_arity_criterion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cfa_arity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ} {k₀ : ℕ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ)
    (hcase : 0 < μ →
      (μ ≤ 1 / 2 ∧ 17 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 2 (13 / 100)) ∨
      (μ ≤ 1 / 4 ∧ 12 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 4 (3 / 25)) ∨
      (μ ≤ 1 / 8 ∧ 10 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 8 (11 / 100))) :
    cfaJoinedBelow f z 1 2 := by
  sorry
/-- States res:constant-factor-path from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.cfa_constant_factor_path in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cfa_constant_factor_path (hext : CFAPathConstruction)
    {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hn : 2 ≤ n) (hmonic : f.Monic) (hdeg : f.natDegree = n)
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    cfaJoinedAtMost f z (2 * μ) ((71 / 10) * μ ^ ((1 : ℝ) / (n : ℝ))) ∧
      (μ ≤ 1 / 2 → cfaJoinedBelow f z 1 5.7) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsZA

namespace PalomarCorpus.E1041.PaperStatementsY
open Polynomial
open scoped NNReal
open scoped ENNReal
open scoped BigOperators
export PalomarCorpus.E1041_02.Shared (cfaJoinedBelow)
/-- **External input for `res:constant-factor-capacity`.** The averaging proof of `res:constant-factor-path`, rerun on the component `C` of `{|f| < 2μ}` containing the first-merge critical point, with the global area input replaced by the component form `Area(C) ≤ π cap(closure C)² = π κ²(2μ)^{2/n}` of the area-capacity inequality, at `λ = 2`, `r = 1/20`. `κ` is the paper's capacity ratio `cap(closure C)/(2μ)^{1/n}`; the pinned Mathlib has no logarithmic capacity, so `κ` enters as the real parameter this hypothesis is stated for. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.CFACapacityConstruction, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CFACapacityConstruction (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (κ : ℝ) (k₀ : ℕ) : Prop :=
  cfaJoinedBelow f z 1
    (Real.sqrt (2 / (k₀ : ℝ)) *
      (Real.sqrt 2 * (1 / 20) / (1 - 1 / 20) ^ 2 +
        κ * (Real.sqrt (Real.log 40) + Real.pi / Real.sqrt (Real.log 2))))
/-- The paper's `A = 283/3610` and `B = 52029/9100`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaA, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaA : ℝ := 283 / 3610
/-- Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaB, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaB : ℝ := 52029 / 9100
/-- The paper's threshold `τ_k = (√(2k) - A)/B`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaTau, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaTau (k : ℕ) : ℝ := (Real.sqrt (2 * (k : ℝ)) - cfaA) / cfaB
/-- States res:constant-factor-capacity from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.cfa_capacity_criterion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cfa_capacity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {κ : ℝ} {k₀ : ℕ}
    (hk₀ : 2 ≤ k₀) (hκ0 : 0 ≤ κ) (hκ : κ ≤ cfaTau k₀)
    (hext : CFACapacityConstruction n f z κ k₀) :
    cfaJoinedBelow f z 1 2 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsY

namespace PalomarCorpus.E1041.PaperStatementsZB
open Set
open MeasureTheory
open Polynomial
open scoped ComplexConjugate
open scoped BigOperators
export PalomarCorpus.E1041_02.Shared (ConnectedAtMost CriticalMinimum)
/-- The half-perimeter property of a set `U`: every point of `U` is joined to every point of its frontier, inside the sublevel set `{|f| ≤ R}`, by a rectifiable path of length at most half of `H¹(∂U)`. For a Jordan domain the paper proves it by choosing one of the two boundary arcs, which needs the Jordan curve theorem; here the property is a hypothesis. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.HalfPerimeterJoin, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfPerimeterJoin (f : ℂ → ℂ) (R : ℝ) (U : Set ℂ) : Prop :=
  ∀ H : ℝ, μH[(1 : ℝ)] (frontier U) ≤ ENNReal.ofReal H →
    ∀ p ∈ U, ∀ q ∈ frontier U, ConnectedAtMost f R (H / 2) p q
/-- The paper's conclusion: two distinct roots joined inside `{|f| ≤ R}` by a rectifiable path of length at most `L`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.HasDistinctConnectionAtMost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasDistinctConnectionAtMost (f : ℂ → ℂ) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ f a = 0 ∧ f b = 0 ∧ ConnectedAtMost f R L a b
/-- The classical input of stage 1: at the first critical level the sublevel set has two distinct one-root components `U_a`, `U_b` whose closures meet at a critical point, each of perimeter at most `P` and each with the half-perimeter joining property. It packages the component-wise Riemann-Hurwitz count of Ebenfelt, Khavinson and Shapiro, the continuous extension of the inverse branch at a critical point, lower semicontinuity of length under uniform convergence, and the Jordan curve theorem. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.SubcriticalSplitExists, restated so the compared statements elaborate against Mathlib alone. -/
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

namespace PalomarCorpus.E1041.CubicPath
open Finset
open Polynomial Set
open scoped BigOperators
open Polynomial
open scoped ComplexConjugate
open scoped ENNReal
open Polynomial Metric
open Polynomial Set
open scoped BigOperators
/-- The two-segment path from a to b through the hub c, defined for every real t by c + max (1 - t) 0 * (a - c) + max (t - 1) 0 * (b - c) with the real coefficients cast into the complex numbers; it equals a at t = 0, the hub c at t = 1, and b at t = 2, and the clamped coefficients make it continuous and piecewise affine on the whole real line. -/
noncomputable def hub (a c b : ℂ) (t : ℝ) : ℂ :=
  c + ((max (1 - t) 0 : ℝ) : ℂ) * (a - c) +
    ((max (t - 1) 0 : ℝ) : ℂ) * (b - c)
/-- For a monic cubic p presented as the product over i in Fin 3 of (X - C (z i)) whose three listed roots all have modulus strictly below 1, there are distinct indices i, j and a hub c such that hub (z i) c (z j) is continuous, has bounded variation on Icc 0 2, satisfies ‖p.eval (hub (z i) c (z j) t)‖ < 1 for every t in Icc 0 2, and has extended variation strictly below ENNReal.ofReal 2; a second existential gives some curve γ continuous on Icc 0 2 with γ 0 = z i, γ 2 = z j and the same containment and variation bounds, without asserting that γ is that hub path; and Squarefree p implies z i ≠ z j. This is the complete degree-three case of the parent problem in its root-occurrence reading. -/
theorem cubic_paper_complete (p : ℂ[X]) (z : Fin 3 → ℂ)
    (hp : p = ∏ i, (X - C (z i))) (hz : ∀ i, ‖z i‖ < 1) :
    ∃ i j : Fin 3, ∃ c : ℂ, i ≠ j ∧
      Continuous (hub (z i) c (z j)) ∧
      BoundedVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub (z i) c (z j) t)‖ < 1) ∧
        eVariationOn (hub (z i) c (z j)) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = z i ∧ γ 2 = z j ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → z i ≠ z j) := by
  sorry
/-- The same degree-three theorem with the cubic given by monicity and degree in place of a root list: for monic p of natural degree 3 every zero of which has modulus strictly below 1, there are zeros a and b of p and a hub c such that hub a c b is continuous, has bounded variation on Icc 0 2, satisfies ‖p.eval (hub a c b t)‖ < 1 for every t in Icc 0 2, and has extended variation strictly below ENNReal.ofReal 2; a second existential gives some curve γ continuous on Icc 0 2 with γ 0 = a, γ 2 = b and the same bounds, without asserting that γ is that hub path. Squarefree p gives a ≠ b; without it a and b may coincide, the degenerate repeated-root case joined by a constant path. -/
theorem monic_cubic_connector (p : ℂ[X]) (hm : p.Monic)
    (hd : p.natDegree = 3) (hz : ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1) :
    ∃ a b c : ℂ, p.eval a = 0 ∧ p.eval b = 0 ∧
      Continuous (hub a c b) ∧
      BoundedVariationOn (hub a c b) (Icc (0 : ℝ) 2) ∧
      ((∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (hub a c b t)‖ < 1) ∧
        eVariationOn (hub a c b) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
        γ 0 = a ∧ γ 2 = b ∧
        (∀ t ∈ Icc (0 : ℝ) 2, ‖p.eval (γ t)‖ < 1) ∧
        BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
        eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal 2) ∧
      (Squarefree p → a ≠ b) := by
  sorry
/-- Translated cubic quotient fibres. Let `q ≥ 2`, let `h` be a complex centre and let `P` be a monic complex polynomial of natural degree 3. Suppose every zero `z` of `z ↦ P.eval ((z - h) ^ q)` has modulus strictly below 1, and that this function has two distinct zeros. Then it has two distinct zeros `a` and `b` such that the two-segment path `hub a h b` from `a` through the centre `h` to `b` satisfies `‖P.eval ((hub a h b t - h) ^ q)‖ < 1` for every `t` in `Icc 0 2` and has extended variation strictly below `ENNReal.ofReal 2` on `Icc 0 2`. The factorisation of `P`, the bounds on its roots and the choice of the two zeros are derived in the proof; none of them is a hypothesis. -/
theorem complete_translated_cubic_quotient_fibres
    {q : ℕ} (hq : 2 ≤ q) (h : ℂ) (P : ℂ[X])
    (hP : P.Monic) (hdeg : P.natDegree = 3)
    (hdisk : ∀ z : ℂ, P.eval ((z - h) ^ q) = 0 → ‖z‖ < 1)
    (htwo : ∃ a b : ℂ, a ≠ b ∧
      P.eval ((a - h) ^ q) = 0 ∧ P.eval ((b - h) ^ q) = 0) :
    ∃ a b : ℂ, a ≠ b ∧ P.eval ((a - h) ^ q) = 0 ∧
      P.eval ((b - h) ^ q) = 0 ∧
      (∀ t ∈ Icc (0 : ℝ) 2, ‖P.eval ((hub a h b t - h) ^ q)‖ < 1) ∧
      eVariationOn (hub a h b) (Icc (0 : ℝ) 2) < ENNReal.ofReal 2 := by
  sorry
end PalomarCorpus.E1041.CubicPath
