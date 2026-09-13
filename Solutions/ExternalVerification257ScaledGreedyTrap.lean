import Mathlib
import Erdos257PeriodNoncollapse.GreedyTrapDynamics

namespace Erdos249257.ExternalVerification257ScaledGreedyTrap

open Set
open Filter Topology
open scoped BigOperators

noncomputable section

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def scaledGreedyRemainder (x : ℝ) (N : ℕ) : ℝ :=
  (2 : ℝ) ^ N * greedyMersenneRemainder x N

noncomputable def mersenneScale (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * mersenneWeight n

noncomputable def ScaledGreedyLowerBranchCofinally (x : ℝ) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    2 * scaledGreedyRemainder x N < mersenneScale (N + 1)

noncomputable def ScaledGreedyRemainderCofinallyBounded (x : ℝ) : Prop :=
  ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ scaledGreedyRemainder x N ≤ B

private theorem greedyRemainder_transport (x : ℝ) (n : ℕ) :
    greedyMersenneRemainder x n =
      Erdos257PeriodNoncollapse.greedyMersenneRemainder x n := by
  induction n with
  | zero =>
      simp only [greedyMersenneRemainder,
        Erdos257PeriodNoncollapse.greedyMersenneRemainder]
  | succ n ih =>
      simp only [greedyMersenneRemainder,
        Erdos257PeriodNoncollapse.greedyMersenneRemainder, ih,
        show mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight from rfl]

private theorem scaledGreedyRemainder_transport :
    scaledGreedyRemainder = Erdos257PeriodNoncollapse.scaledGreedyRemainder := by
  funext x N
  simp only [scaledGreedyRemainder, Erdos257PeriodNoncollapse.scaledGreedyRemainder,
    greedyRemainder_transport]

private theorem scaledGreedyLowerBranchCofinally_transport :
    ScaledGreedyLowerBranchCofinally =
      Erdos257PeriodNoncollapse.ScaledGreedyLowerBranchCofinally := by
  funext x
  simp only [ScaledGreedyLowerBranchCofinally,
    Erdos257PeriodNoncollapse.ScaledGreedyLowerBranchCofinally,
    scaledGreedyRemainder_transport,
    show mersenneScale = Erdos257PeriodNoncollapse.mersenneScale from rfl]

private theorem scaledGreedyRemainderCofinallyBounded_transport :
    ScaledGreedyRemainderCofinallyBounded =
      Erdos257PeriodNoncollapse.ScaledGreedyRemainderCofinallyBounded := by
  funext x
  simp only [ScaledGreedyRemainderCofinallyBounded,
    Erdos257PeriodNoncollapse.ScaledGreedyRemainderCofinallyBounded,
    scaledGreedyRemainder_transport]

private theorem mersenneAchievementSet_transport :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := rfl

theorem scaledGreedyRemainder_tendsto_atTop_of_not_mem {x : ℝ} (hx : 0 ≤ x)
    (hnot : x ∉ mersenneAchievementSet) :
    Tendsto (fun N : ℕ => scaledGreedyRemainder x N) atTop atTop := by
  rw [mersenneAchievementSet_transport] at hnot
  rw [scaledGreedyRemainder_transport]
  exact Erdos257PeriodNoncollapse.scaledGreedyRemainder_tendsto_atTop_of_not_mem hx hnot

theorem mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded {x : ℝ}
    (hx : 0 ≤ x) :
    x ∈ mersenneAchievementSet ↔ ScaledGreedyRemainderCofinallyBounded x := by
  rw [mersenneAchievementSet_transport, scaledGreedyRemainderCofinallyBounded_transport]
  exact Erdos257PeriodNoncollapse.mem_mersenneAchievementSet_iff_scaledRemainder_cofinallyBounded hx

theorem mersenneAchievementSet_eq_scaledGreedyTrap :
    mersenneAchievementSet =
      {x : ℝ | 0 ≤ x ∧ ∀ N : ℕ, scaledGreedyRemainder x N < 2} := by
  rw [mersenneAchievementSet_transport, scaledGreedyRemainder_transport]
  exact Erdos257PeriodNoncollapse.mersenneAchievementSet_eq_scaledGreedyTrap

theorem rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (q : ℝ) := by
  rw [mersenneAchievementSet_transport, scaledGreedyLowerBranchCofinally_transport]
  exact
    Erdos257PeriodNoncollapse.rat_mem_mersenneAchievementSet_iff_scaledLowerBranchCofinally
      q hq

theorem one_div_twentyOne_mem_iff_scaledLowerBranchCofinally :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyLowerBranchCofinally (1 / 21 : ℝ) := by
  rw [mersenneAchievementSet_transport, scaledGreedyLowerBranchCofinally_transport]
  exact Erdos257PeriodNoncollapse.one_div_twentyOne_mem_iff_scaledLowerBranchCofinally

theorem one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ScaledGreedyRemainderCofinallyBounded (1 / 21 : ℝ) := by
  rw [mersenneAchievementSet_transport, scaledGreedyRemainderCofinallyBounded_transport]
  exact Erdos257PeriodNoncollapse.one_div_twentyOne_mem_iff_scaledRemainder_cofinallyBounded

end

end Erdos249257.ExternalVerification257ScaledGreedyTrap
