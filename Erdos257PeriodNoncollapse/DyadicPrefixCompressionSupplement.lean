import Erdos257PeriodNoncollapse.GreedyAchievementSet
import Erdos257PeriodNoncollapse.HalfCutLocator
import Erdos257PeriodNoncollapse.RationalSupportCarrySkeleton
import Erdos257PeriodNoncollapse.DyadicPrefixCompression

/-
The paper repository's copy of this module does not declare the results below; they were proved in
this corpus. A shim can only publish a name the library has, so this module keeps them, and keeps them
exactly as they were written: it is the corpus module with every declaration the library already carries
removed, and the shim imported in their place. No statement, hypothesis, proof or name is changed here.
-/

/-!
# Dyadic prefix compression

This module owns the corrected transport from a reduced finite Mersenne prefix to the residual
support fraction and its wrap-ratio bound.
The reusable core is stated for an arbitrary finite positive fragment, not
only for an initial segment.

No novelty or priority claim is made for the statements in this file.  Nothing here proves or
refutes the universal Erdős #257 problem.
-/

namespace Erdos257PeriodNoncollapse

open Set

/-! ## Pure reduced-denominator transport -/

/-- Empty rational prefix: no selected exponent through rank `0`. -/
theorem greedyMersennePrefixRat_zero (x : ℚ) :
    greedyMersennePrefixRat x 0 = ∅ := by
  simp [greedyMersennePrefixRat]

/-- The displayed half prefix at rank `0` is the empty finite sum. -/
theorem halfGreedyPrefixRat_zero : halfGreedyPrefixRat 0 = 0 := by
  simp [halfGreedyPrefixRat, greedyMersennePrefixRat_zero, finiteErdosSum]

/-- Empty prefix residual `1/2` is dyadically safe at rank `1`.
Lean 4.30 `norm_num` does not close the empty `Finset.range 0` unfolding. -/
theorem halfGreedy_BlockDyadicSafeAt_zero :
    BlockDyadicSafeAt
      (halfGreedyResidualDisplayedNumerator 0).natAbs
      (halfGreedyPrefixDenominator 0) 1 := by
  simp [BlockDyadicSafeAt, halfGreedyResidualDisplayedNumerator,
    halfGreedyPrefixDenominator, halfGreedyPrefixRat_zero]

end Erdos257PeriodNoncollapse
