/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band a

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial
open Set
open scoped ComplexConjugate
open scoped BigOperators
open scoped NNReal
open scoped ENNReal

namespace PalomarCorpus.E1041.PaperStatementsZA
open Polynomial
open Set
open scoped ComplexConjugate
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
/-- A closed sublevel connector, allowing the zero-length repeated-root case. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ConnectedAtMost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedAtMost (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧ γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ ≤ R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.CriticalMinimum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalMinimum (p : ℂ[X]) (μ : ℝ) : Prop :=
  IsLeast {x : ℝ | ∃ c : ℂ, p.derivative.eval c = 0 ∧ x = ‖p.eval c‖} μ
/-- The geometric conclusion used by the paper: a continuous rectifiable curve with specified endpoints, containment at every parameter, and a strict variation bound. Local copy of ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.HasDistinctConnection, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasDistinctConnection (p : ℂ[X]) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ p.eval a = 0 ∧ p.eval b = 0 ∧ ConnectedBelow p.eval R L a b
/-- Target shared by both `res:low-critical-thirteen-twentyfifths` rows. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.LowCriticalThirteenTwentyFifths, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def LowCriticalThirteenTwentyFifths : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ → μ ≤ 13 / 25 → HasDistinctConnection p 1 2
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.RootEnumeration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RootEnumeration {n : ℕ} (p : ℂ[X]) (z : Fin n → ℂ) : Prop :=
  p = ∏ i, (X - C (z i))
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.RootsInOpenUnitDisc, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RootsInOpenUnitDisc (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1
/-- Main bound in both scale-free corollaries. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ScaledLowCritical, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ScaledLowCritical : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      (2 * (((25 / 13 : ℝ) * μ) ^ (1 / (p.natDegree : ℝ))))
/-- The additional `5/2` bound in the short-note scaling corollary. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ScaledLowCriticalFiveHalves, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ScaledLowCriticalFiveHalves : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      ((5 / 2 : ℝ) * (μ ^ (1 / (p.natDegree : ℝ))))
/-- Two zero occurrences joined by a path of length at most `L` inside the OPEN sublevel set `{|f| < R}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaJoinedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaJoinedBelow {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧
    (∃ γ : ℝ → ℂ, ContinuousOn γ (Set.Icc (0 : ℝ) 2) ∧ γ 0 = z i ∧ γ 2 = z j ∧
      (∀ t ∈ Set.Icc (0 : ℝ) 2, ‖f.eval (γ t)‖ < R) ∧
      BoundedVariationOn γ (Set.Icc (0 : ℝ) 2) ∧
      eVariationOn γ (Set.Icc (0 : ℝ) 2) ≤ ENNReal.ofReal L) ∧
    (Squarefree f → z i ≠ z j)
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
/-- **External input for `res:constant-factor-path`.** The paper's construction: for a squarefree monic `f` of degree `n ≥ 3` with least critical modulus `μ > 0`, every `r ∈ (0,1)` and `λ > 1` give a selected component with `k ≥ 2` roots and a path in `{|f| < λμ}` between two zero occurrences of length at most the bracket (CF) times `ρ = μ^{1/n}`. Its ingredients are Pólya's area inequality, the Koebe distortion theorem, the coarea formula with the boundary identity `|dz| = σ dφ/|f'|` and total argument variation `2πk'`, the area formula for the disjoint images of the univalent inverse branches, and the mean-value selection of a regular level and of a direction avoiding the critical-value arguments. The containment is strict because the proof selects a regular level strictly inside its positive-measure window, which is what the paper's own `{|f| < 1}` clause uses. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.CFAPathConstruction, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CFAPathConstruction : Prop :=
  ∀ (n : ℕ) (f : ℂ[X]) (z : Fin n → ℂ) (μ lam r : ℝ),
    3 ≤ n → f.Monic → f.natDegree = n → RootEnumeration f z →
    CriticalMinimum f μ → 0 < μ → 0 < r → r < 1 → 1 < lam →
    ∃ k : ℕ, 2 ≤ k ∧
      cfaJoinedBelow f z (lam * μ) (cfaBracket n k lam r * μ ^ ((1 : ℝ) / (n : ℝ)))
/-- The paper's normalised critical-value separation at a real centre `w₀`: every OTHER critical point `d` satisfies `|f(d)/f(c) - w₀| ≥ S`. For `w₀ = 1` this is `ConnectorR18.ValueSeparatedAt`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.ValueSeparatedAtCentre, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ValueSeparatedAtCentre (f : ℂ[X]) (c : ℂ) (w₀ S : ℝ) : Prop :=
  ∀ d : ℂ, f.derivative.eval d = 0 → d ≠ c → S ≤ ‖f.eval d / f.eval c - (w₀ : ℂ)‖
/-- The right side of the paper's displayed bound `eq:disk-family-length`, without the `2|v|^{2/n}` prefactor: `(S/(n-1))^{2/n} log((S² + S + p)/(S² - S + p))`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separationCoefficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def separationCoefficient (n : ℕ) (S p : ℝ) : ℝ :=
  (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
    Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))
/-- **The external analytic input**: the paper's Theorem `res:critical-value-separation` (separation of one simple critical value). `f` monic of degree `n ≥ 3`, `c` a simple critical point with `v = f(c) ≠ 0`, `w₀ ∈ [0,1]`, `S > max(w₀, 1-w₀)`, and every other critical point `d` obeying `|f(d)/v - w₀| ≥ S`; then two distinct roots are joined inside `{|f| ≤ |v|}` by a curve `Γ` with `length(Γ)² ≤ 2|v|^{2/n}(S/(n-1))^{2/n} log((S²+S+p)/(S²-S+p))`, `p = w₀(1-w₀)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.CriticalValueSeparationTheorem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalValueSeparationTheorem : Prop :=
  ∀ (f : ℂ[X]) (c : ℂ) (w₀ S : ℝ), f.Monic → 3 ≤ f.natDegree →
    f.derivative.eval c = 0 → f.derivative.derivative.eval c ≠ 0 →
    f.eval c ≠ 0 → 0 ≤ w₀ → w₀ ≤ 1 → max w₀ (1 - w₀) < S →
    ValueSeparatedAtCentre f c w₀ S →
    ∃ a b : ℂ, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ConnectedAtMost f.eval ‖f.eval c‖
        (Real.sqrt (2 * ‖f.eval c‖ ^ ((2 : ℝ) / (f.natDegree : ℝ)) *
          separationCoefficient f.natDegree S (w₀ * (1 - w₀)))) a b
/-- Two zero occurrences joined by a path of length at most `L` inside the closed sublevel set `{|f| ≤ R}`, with distinct locations when `f` is squarefree. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.cfaJoinedAtMost, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cfaJoinedAtMost {n : ℕ} (f : ℂ[X]) (z : Fin n → ℂ) (R L : ℝ) : Prop :=
  ∃ i j : Fin n, i ≠ j ∧ ConnectedAtMost f.eval R L (z i) (z j) ∧
    (Squarefree f → z i ≠ z j)
/-- States res:separation-parent from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separation_parent in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem separation_parent (hSep : CriticalValueSeparationTheorem)
    {f : ℂ[X]} {c : ℂ} {w₀ S : ℝ}
    (hmonic : f.Monic) (hdeg : 3 ≤ f.natDegree)
    (hroots : RootsInOpenUnitDisc f)
    (hcrit : f.derivative.eval c = 0) (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv0 : f.eval c ≠ 0) (hv1 : ‖f.eval c‖ < 1)
    (hw0 : 0 ≤ w₀) (hw1 : w₀ ≤ 1) (hS : 4 / 3 ≤ S)
    (hsep : ValueSeparatedAtCentre f c w₀ S) :
    HasDistinctConnection f 1 2 := by
  sorry
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
/-- States res:scaled-low-critical, res:scaled-low-critical-path from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCriticalFiveHalves_of_lowCritical in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaledLowCriticalFiveHalves_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCriticalFiveHalves := by
  sorry
/-- States res:low-critical-scale-free, res:scaled-low-critical from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCritical_of_lowCritical in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaledLowCritical_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCritical := by
  sorry
end PalomarCorpus.E1041.PaperStatementsZA
