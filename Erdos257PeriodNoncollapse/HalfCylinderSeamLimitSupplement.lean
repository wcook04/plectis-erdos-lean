import Erdos257PeriodNoncollapse.HalfCylinderFloorErrorReset
import Erdos257PeriodNoncollapse.HalfCylinderSeamLimit

/-
The paper repository's copy of this module does not declare the results below; they were proved in
this corpus. A shim can only publish a name the library has, so this module keeps them, and keeps them
exactly as they were written: it is the corpus module with every declaration the library already carries
removed, and the shim imported in their place. No statement, hypothesis, proof or name is changed here.
-/

/-!
# Closed-set seam-limit route for the half target

The actual rational greedy orbit is not needed if the integer seam words
themselves approach the half target.  This module makes that alternate route
exact.  It proves that the empirical exponential remainder bound

`seamIntegerGreedyRemainder s < 2^(s+1)`

forces the finite seam support values to converge to `1/2`; closedness of the
Mersenne achievement set then gives exact membership.  The bound is exposed
as an honest socket and is not asserted here.
-/

namespace Erdos257PeriodNoncollapse

open Set Filter
open HalfCylinderIntegerGreedy

/-! ## Finite seam values -/

/-- The concrete cofinal small-remainder hypothesis isolated by the exact
floor-defect argument: beyond every requested row there is a later seam row
whose integer remainder is at most linear. -/
def SeamGreedyRemainderLinearCofinal : Prop :=
  ∀ N : ℕ, ∃ s : ℕ, N ≤ s ∧
    seamIntegerGreedyRemainder s ≤ 2 * s + 4

/-- A linear numerator is negligible on the row-square scale `4^s`. -/
theorem tendsto_linearSeamBound_div_fourPow_zero :
    Tendsto
      (fun s : ℕ => ((2 * s + 4 : ℕ) : ℝ) / (4 : ℝ) ^ s)
      atTop (nhds 0) := by
  have hpow : Tendsto (fun s : ℕ => (1 / 4 : ℝ) ^ s)
      atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
  have hself : Tendsto
      (fun s : ℕ => (s : ℝ) * (1 / 4 : ℝ) ^ s)
      atTop (nhds 0) :=
    tendsto_self_mul_const_pow_of_lt_one
      (by norm_num : (0 : ℝ) ≤ 1 / 4)
      (by norm_num : (1 / 4 : ℝ) < 1)
  have hlinear := (hself.const_mul 2).add (hpow.const_mul 4)
  convert hlinear using 1
  · funext s
    push_cast
    rw [div_eq_mul_inv, ← inv_pow]
    ring
  · norm_num

/-- Cofinal linear seam remainders produce a concrete cofinal
subquadratic sequence. -/
theorem exists_seamGreedyRemainderSubquadraticAlong_of_linearCofinal
    (hlinear : SeamGreedyRemainderLinearCofinal) :
    ∃ rows : ℕ → ℕ, SeamGreedyRemainderSubquadraticAlong rows := by
  classical
  let rows : ℕ → ℕ := fun N => Classical.choose (hlinear N)
  have hrowData : ∀ N : ℕ,
      N ≤ rows N ∧
        seamIntegerGreedyRemainder (rows N) ≤ 2 * rows N + 4 := by
    intro N
    exact Classical.choose_spec (hlinear N)
  have hrows : Tendsto rows atTop atTop := by
    rw [tendsto_atTop]
    intro N
    filter_upwards [eventually_ge_atTop N] with j hj
    exact hj.trans (hrowData j).1
  refine ⟨rows, hrows, ?_⟩
  have hupper := tendsto_linearSeamBound_div_fourPow_zero.comp hrows
  have hnonneg : ∀ᶠ j in atTop,
      0 ≤ seamGreedyNormalizedRemainder (rows j) :=
    Filter.Eventually.of_forall fun j => by
      exact div_nonneg (by positivity) (by positivity)
  have hle : ∀ᶠ j in atTop,
      seamGreedyNormalizedRemainder (rows j) ≤
        ((2 * rows j + 4 : ℕ) : ℝ) / (4 : ℝ) ^ rows j :=
    Filter.Eventually.of_forall fun j => by
      unfold seamGreedyNormalizedRemainder
      exact div_le_div_of_nonneg_right
        (by exact_mod_cast (hrowData j).2) (by positivity)
  exact squeeze_zero' hnonneg hle (by
    simpa only [Function.comp_apply] using hupper)

/-- The cofinal linear branch of the floor-defect dichotomy already gives an
exact half representation.  No conclusion is drawn here from its eventual
large-remainder complement. -/
theorem half_mem_mersenneAchievementSet_of_linearCofinal
    (hlinear : SeamGreedyRemainderLinearCofinal) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  obtain ⟨rows, hrows⟩ :=
    exists_seamGreedyRemainderSubquadraticAlong_of_linearCofinal hlinear
  exact half_mem_mersenneAchievementSet_of_subquadraticAlong rows hrows

/-! ## The exact upper-bound socket -/

end Erdos257PeriodNoncollapse
