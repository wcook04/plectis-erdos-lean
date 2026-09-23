/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusCarry
import Erdos249257.CertificateKernel
import Erdos249257.GreedyAchievementSet
import ErdosProblems.Erdos257.PaperCompleteR20.GeneralRepairCorrespondence
import Solutions.PalomarCorpus.E257_39.Statement

open ArithmeticFunction
open Filter
open Set
open scoped ArithmeticFunction.Moebius
open scoped ENNReal
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsM
export PalomarCorpus.E257_39.Shared (mersenneAchievementSet mersenneWeight positiveMersenneSupportValue supportCoeff)

theorem paper_general_repair_criteria {x : ℝ} (hx : 0 ≤ x) :
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N) ∧
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      N < K+2*Nat.sqrt K+12 ∧ paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos257.PaperCompleteR20.paper_general_repair_criteria x hx

end PalomarCorpus.E257.PaperStatementsM
