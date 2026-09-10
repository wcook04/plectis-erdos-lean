import Mathlib
import Erdos257PeriodNoncollapse.GreedyAchievementSet

/-!
# Source transport for the rational greedy-skip membership criterion

The compared statements are transported from
`Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport_infinite_iff_cofinal_skips`,
`infinite_greedyMersenneSkippedSupport_of_rat_mem`,
`rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite`, and
`rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips`.
-/

namespace Erdos249257.ExternalVerification257RationalMembership

open Set

noncomputable section

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}

noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}

theorem mersenneWeight_eq :
    mersenneWeight = Erdos257PeriodNoncollapse.mersenneWeight :=
  rfl

theorem greedyMersenneRemainder_eq :
    greedyMersenneRemainder = Erdos257PeriodNoncollapse.greedyMersenneRemainder := by
  funext x n
  induction n with
  | zero => rfl
  | succ n ih =>
    show (if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else greedyMersenneRemainder x n) = _
    rw [ih, mersenneWeight_eq]
    rfl

theorem greedyMersenneSupport_eq :
    greedyMersenneSupport = Erdos257PeriodNoncollapse.greedyMersenneSupport := by
  funext x
  simp only [greedyMersenneSupport, Erdos257PeriodNoncollapse.greedyMersenneSupport,
    mersenneWeight_eq, greedyMersenneRemainder_eq]

theorem greedyMersenneSkippedSupport_eq :
    greedyMersenneSkippedSupport =
      Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport := by
  funext x
  simp only [greedyMersenneSkippedSupport,
    Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport,
    greedyMersenneSupport_eq]

theorem positiveMersenneSupportValue_eq :
    positiveMersenneSupportValue =
      Erdos257PeriodNoncollapse.positiveMersenneSupportValue := by
  funext A
  simp only [positiveMersenneSupportValue,
    Erdos257PeriodNoncollapse.positiveMersenneSupportValue, mersenneWeight_eq]

theorem mersenneAchievementSet_eq :
    mersenneAchievementSet = Erdos257PeriodNoncollapse.mersenneAchievementSet := by
  simp only [mersenneAchievementSet, Erdos257PeriodNoncollapse.mersenneAchievementSet,
    positiveMersenneSupportValue_eq]

theorem greedyMersenneSkippedSupport_infinite_iff_cofinal_skips (x : ℝ) :
    (greedyMersenneSkippedSupport x).Infinite ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n := by
  rw [greedyMersenneSkippedSupport_eq, mersenneWeight_eq, greedyMersenneRemainder_eq]
  exact Erdos257PeriodNoncollapse.greedyMersenneSkippedSupport_infinite_iff_cofinal_skips x

theorem infinite_greedyMersenneSkippedSupport_of_rat_mem
    {q : ℚ} (hmem : (q : ℝ) ∈ mersenneAchievementSet) :
    (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  rw [mersenneAchievementSet_eq] at hmem
  rw [greedyMersenneSkippedSupport_eq]
  exact Erdos257PeriodNoncollapse.infinite_greedyMersenneSkippedSupport_of_rat_mem hmem

theorem rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (q : ℝ)).Infinite := by
  rw [mersenneAchievementSet_eq, greedyMersenneSkippedSupport_eq]
  exact Erdos257PeriodNoncollapse.rat_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite
    q hq

theorem rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips
    (q : ℚ) (hq : 0 ≤ q) :
    (q : ℝ) ∈ mersenneAchievementSet ↔
      ∀ K : ℕ, ∃ n : ℕ, K ≤ n ∧
        ¬ mersenneWeight (n + 1) ≤
          greedyMersenneRemainder (q : ℝ) n := by
  rw [mersenneAchievementSet_eq, mersenneWeight_eq, greedyMersenneRemainder_eq]
  exact Erdos257PeriodNoncollapse.rat_mem_mersenneAchievementSet_iff_cofinal_greedy_skips
    q hq

end

end Erdos249257.ExternalVerification257RationalMembership
