/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CampbellShiftSynchronization
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCylinderFixedTailSocket
import Erdos249257.HalfCylinderHalfMembershipClassification

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CampbellShiftSynchronization`, `Erdos249257.GreedyAchievementSet`,
`Erdos249257.HalfCylinderFixedTailSocket`,
`Erdos249257.HalfCylinderHalfMembershipClassification`.
-/

open Set
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
open scoped Classical

namespace Erdos249257.ExternalVerification257PaperStatementsG

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def GreedyMersenneFatalAt (x : ℝ) (n : ℕ) : Prop :=
  mersenneTail n < greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

noncomputable def IsLastHalfGreedySkip (M : ℕ) : Prop :=
  M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
    ∀ m, M < m → m ∉ greedyMersenneSkippedSupport (1 / 2 : ℝ)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

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

end Erdos249257.ExternalVerification257PaperStatementsG
