/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CampbellShiftSynchronization
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderFixedTailSocket
import Erdos249257.HalfCylinderHalfMembershipClassification
import Solutions.PalomarCorpus.E257g.Statement

open Set
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
open scoped Classical

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsG

theorem half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ ∃ M : ℕ, IsLastHalfGreedySkip M := by
  set_option smartUnfolding false in
  exact @Erdos249257.half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip

theorem isLastHalfGreedySkip_iff_skip_and_fatal
    {M : ℕ} :
    IsLastHalfGreedySkip M ↔
      M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
        GreedyMersenneFatalAt (1 / 2 : ℝ) M := by
  set_option smartUnfolding false in
  exact @Erdos249257.isLastHalfGreedySkip_iff_skip_and_fatal M

end PalomarCorpus.E257.PaperStatementsG
