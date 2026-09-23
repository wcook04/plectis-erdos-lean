/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperCompleteR21.ConstantFactorAreaCriteria
import ErdosProblems.Erdos1041.PaperCompleteR21.LowCriticalScaleTransport
import ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent
import ErdosProblems.Erdos1041.PaperCurveAssembly
import Solutions.PalomarCorpus.E1041_02.Statement

open Polynomial
open Set
open scoped ComplexConjugate
open scoped BigOperators
open scoped NNReal
open scoped ENNReal

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsZA
export PalomarCorpus.E1041_02.Shared (ConnectedAtMost CriticalMinimum cfaJoinedBelow)

noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L

noncomputable def HasDistinctConnection (p : ℂ[X]) (R L : ℝ) : Prop :=
  ∃ a b : ℂ, a ≠ b ∧ p.eval a = 0 ∧ p.eval b = 0 ∧ ConnectedBelow p.eval R L a b

noncomputable def LowCriticalThirteenTwentyFifths : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ → μ ≤ 13 / 25 → HasDistinctConnection p 1 2

noncomputable def RootsInOpenUnitDisc (p : ℂ[X]) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z‖ < 1

noncomputable def ScaledLowCritical : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      (2 * (((25 / 13 : ℝ) * μ) ^ (1 / (p.natDegree : ℝ))))

noncomputable def ScaledLowCriticalFiveHalves : Prop :=
  ∀ (p : ℂ[X]) (μ : ℝ), p.Monic → Squarefree p → 2 ≤ p.natDegree →
    CriticalMinimum p μ →
    HasDistinctConnection p ((25 / 13 : ℝ) * μ)
      ((5 / 2 : ℝ) * (μ ^ (1 / (p.natDegree : ℝ))))

noncomputable def ValueSeparatedAtCentre (f : ℂ[X]) (c : ℂ) (w₀ S : ℝ) : Prop :=
  ∀ d : ℂ, f.derivative.eval d = 0 → d ≠ c → S ≤ ‖f.eval d / f.eval c - (w₀ : ℂ)‖

noncomputable def separationCoefficient (n : ℕ) (S p : ℝ) : ℝ :=
  (S / ((n : ℝ) - 1)) ^ ((2 : ℝ) / (n : ℝ)) *
    Real.log ((S ^ 2 + S + p) / (S ^ 2 - S + p))

noncomputable def CriticalValueSeparationTheorem : Prop :=
  ∀ (f : ℂ[X]) (c : ℂ) (w₀ S : ℝ), f.Monic → 3 ≤ f.natDegree →
    f.derivative.eval c = 0 → f.derivative.derivative.eval c ≠ 0 →
    f.eval c ≠ 0 → 0 ≤ w₀ → w₀ ≤ 1 → max w₀ (1 - w₀) < S →
    ValueSeparatedAtCentre f c w₀ S →
    ∃ a b : ℂ, a ≠ b ∧ f.eval a = 0 ∧ f.eval b = 0 ∧
      ConnectedAtMost f.eval ‖f.eval c‖
        (Real.sqrt (2 * ‖f.eval c‖ ^ ((2 : ℝ) / (f.natDegree : ℝ)) *
          separationCoefficient f.natDegree S (w₀ * (1 - w₀)))) a b

theorem separation_parent (hSep : CriticalValueSeparationTheorem)
    {f : ℂ[X]} {c : ℂ} {w₀ S : ℝ}
    (hmonic : f.Monic) (hdeg : 3 ≤ f.natDegree)
    (hroots : RootsInOpenUnitDisc f)
    (hcrit : f.derivative.eval c = 0) (hsimple : f.derivative.derivative.eval c ≠ 0)
    (hv0 : f.eval c ≠ 0) (hv1 : ‖f.eval c‖ < 1)
    (hw0 : 0 ≤ w₀) (hw1 : w₀ ≤ 1) (hS : 4 / 3 ≤ S)
    (hsep : ValueSeparatedAtCentre f c w₀ S) :
    HasDistinctConnection f 1 2 := by
  apply ErdosProblems.Erdos1041.PaperCompleteR21.SeparationParent.separation_parent <;> assumption

theorem cfa_arity_criterion {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ} {k₀ : ℕ}
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ)
    (hcase : 0 < μ →
      (μ ≤ 1 / 2 ∧ 17 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 2 (13 / 100)) ∨
      (μ ≤ 1 / 4 ∧ 12 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 4 (3 / 25)) ∨
      (μ ≤ 1 / 8 ∧ 10 ≤ k₀ ∧ CFAArityConstruction n f z k₀ 8 (11 / 100))) :
    cfaJoinedBelow f z 1 2 := by
  apply ErdosProblems.Erdos1041.PaperCompleteR21.cfa_arity_criterion <;> assumption

theorem cfa_constant_factor_path (hext : CFAPathConstruction)
    {n : ℕ} {f : ℂ[X]} {z : Fin n → ℂ} {μ : ℝ}
    (hn : 2 ≤ n) (hmonic : f.Monic) (hdeg : f.natDegree = n)
    (hz : RootEnumeration f z) (hμ : CriticalMinimum f μ) :
    cfaJoinedAtMost f z (2 * μ) ((71 / 10) * μ ^ ((1 : ℝ) / (n : ℝ))) ∧
      (μ ≤ 1 / 2 → cfaJoinedBelow f z 1 5.7) := by
  apply ErdosProblems.Erdos1041.PaperCompleteR21.cfa_constant_factor_path <;> assumption

theorem scaledLowCriticalFiveHalves_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCriticalFiveHalves := @ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCriticalFiveHalves_of_lowCritical H

theorem scaledLowCritical_of_lowCritical
    (H : LowCriticalThirteenTwentyFifths) : ScaledLowCritical := @ErdosProblems.Erdos1041.PaperCompleteR21.scaledLowCritical_of_lowCritical H

end PalomarCorpus.E1041.PaperStatementsZA
