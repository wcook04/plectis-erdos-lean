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
import Solutions.PalomarCorpus.E1041za.Statement

open Polynomial
open Set
open scoped ComplexConjugate
open scoped BigOperators
open scoped NNReal
open scoped ENNReal

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsZA

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
