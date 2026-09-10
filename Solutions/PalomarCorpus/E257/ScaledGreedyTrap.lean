/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.GreedyTrapDynamics
import Solutions.PalomarCorpus.E257.Shared

open Set
open Filter Topology
open scoped BigOperators

namespace PalomarCorpus.E257.ScaledGreedyTrap
export PalomarCorpus.E257.Shared (greedyMersenneRemainder mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)

noncomputable section

noncomputable def scaledGreedyRemainder (x : ℝ) (N : ℕ) : ℝ :=
  Erdos257PeriodNoncollapse.scaledGreedyRemainder x N

noncomputable def mersenneScale (n : ℕ) : ℝ :=
  Erdos257PeriodNoncollapse.mersenneScale n

noncomputable def ScaledGreedyLowerBranchCofinally (x : ℝ) : Prop :=
  Erdos257PeriodNoncollapse.ScaledGreedyLowerBranchCofinally x

noncomputable def ScaledGreedyRemainderCofinallyBounded (x : ℝ) : Prop :=
  Erdos257PeriodNoncollapse.ScaledGreedyRemainderCofinallyBounded x

theorem scaledGreedyRemainder_tendsto_atTop_of_not_mem {x : ℝ} (hx : 0 ≤ x)
    (hnot : x ∉ mersenneAchievementSet) :
    Tendsto (fun N : ℕ => scaledGreedyRemainder x N) atTop atTop := by
  change Tendsto
    (fun N : ℕ => Erdos257PeriodNoncollapse.scaledGreedyRemainder x N) atTop atTop
  exact Erdos257PeriodNoncollapse.scaledGreedyRemainder_tendsto_atTop_of_not_mem hx hnot

theorem mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded {x : ℝ}
    (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔ ScaledGreedyRemainderCofinallyBounded x := by
  change x ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet ↔
    Erdos257PeriodNoncollapse.ScaledGreedyRemainderCofinallyBounded x
  exact Erdos257PeriodNoncollapse.mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded hx

theorem mersenneAchievementSet_eq_scaledGreedyTrap :
    mersenneAchievementSet =
      {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ, scaledGreedyRemainder x N < 2} := by
  change Erdos257PeriodNoncollapse.mersenneAchievementSet =
    {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ,
      Erdos257PeriodNoncollapse.scaledGreedyRemainder x N < 2}
  exact Erdos257PeriodNoncollapse.mersenneAchievementSet_eq_scaledGreedyTrap

theorem rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (q : ℝ) := by
  change (q : ℝ) ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet ↔
    Erdos257PeriodNoncollapse.ScaledGreedyLowerBranchCofinally (q : ℝ)
  exact
    Erdos257PeriodNoncollapse.rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
      q hq

theorem one_div_twentyOne_mem_iff_scaledLowerBranchCofinally :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ) := by
  change (1 / 21 : ℝ) ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet ↔
    Erdos257PeriodNoncollapse.ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ)
  exact Erdos257PeriodNoncollapse.one_div_twentyOne_mem_iff_scaledLowerBranchCofinally

theorem one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ) := by
  change (1 / 21 : ℝ) ∈ Erdos257PeriodNoncollapse.mersenneAchievementSet ↔
    Erdos257PeriodNoncollapse.ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ)
  exact Erdos257PeriodNoncollapse.one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded

end

end PalomarCorpus.E257.ScaledGreedyTrap
