/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusCofinalExactRows
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.CertificateKernel
import Erdos249257.CofinalStripReturn
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCutLocator
import Erdos249257.TerminalOnlyCofinal
import ErdosProblems.Erdos257.PaperCompleteR20.SixMembershipConditions
import ErdosProblems.Erdos257.PaperCompleteR21.ExactRowDichotomyCountermodels
import ErdosProblems.Erdos257.PaperCompleteR21.TerminalStripExactRowGap
import Solutions.PalomarCorpus.E257k.Statement

open scoped BigOperators
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsK

theorem six_membership_conditions :
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ N : ℕ, (mobiusCenteredHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        2*Real.sqrt (N : ℝ)+4) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧ 0 < n ∧ n ∉ greedyMersenneSupport (1/2 : ℝ)) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ GreedyHalfCarryCofinalStripReturn) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip) ∧
    ((1/2 : ℝ) ∈ mersenneAchievementSet ↔
      (∀ n : ℕ, greedyMersenneRemainder (1/2 : ℝ) n ≤ mersenneTail n) ∧
        ¬ ExistsFatalHalfGap) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR20.six_membership_conditions

theorem paper_both_cofinal_statements_iff_half_membership :
    ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ CofinalExactLocalMersenneHalfRows) ∧
      ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ HalfCarryCofinalTerminalOnlyStrip) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_both_cofinal_statements_iff_half_membership

theorem paper_critical_crossing_support_is_greedy_prefix
    {D : Finset ℕ} {c : ℕ} (hc : 4 ≤ c) (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ))
    (hcross : (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c) :
    D = halfGreedyPrefixSupport (c - 1) ∧
      (↑D : Set ℕ) = greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Iic (c - 1) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_crossing_support_is_greedy_prefix D c hc hD hbelow hcross

end PalomarCorpus.E257.PaperStatementsK
