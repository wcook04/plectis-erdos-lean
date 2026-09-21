/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band w

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial
open Set
open Filter
open Metric
open Bornology
open scoped BigOperators
open scoped ComplexConjugate
open scoped Topology

namespace PalomarCorpus.E1041.PaperStatementsW
open Polynomial
open Set
open Filter
open Metric
open Bornology
open scoped BigOperators
open scoped ComplexConjugate
open scoped Topology
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.CriticalEnumeration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.RootsInClosedDisc, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R
/-- Reflected-derivative bound, with the derivative root multiplicities specified by an exact polynomial factorisation. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ReflectedCriticalValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ReflectedCriticalValue : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ), 2 ≤ n → p.Monic →
    p.natDegree = n → RootsInClosedDisc p 0 1 → CriticalEnumeration p c →
      ∀ j, ‖p.eval (c j)‖ ≤ ∏ k, ‖1 - conj (c k) * c j‖
/-- States eq:critical-reflected-product, res:reflected-critical-value from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperReflectedCompletion.reflected_critical_value in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem reflected_critical_value : ReflectedCriticalValue := by
  sorry
end PalomarCorpus.E1041.PaperStatementsW
