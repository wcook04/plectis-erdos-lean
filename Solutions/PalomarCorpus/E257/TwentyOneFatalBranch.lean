/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.TwentyOneQuotientGreedy
import Solutions.PalomarCorpus.E257.Shared

namespace PalomarCorpus.E257.TwentyOneFatalBranch
export PalomarCorpus.E257.Shared (greedyMersenneRemainder greedyMersenneSkippedSupport greedyMersenneSupport integerGreedyBits mersenneAchievementSet mersenneWeight mersenneWeightRat positiveMersenneSupportValue)

noncomputable section

noncomputable abbrev mersenneTail := Erdos257PeriodNoncollapse.mersenneTail
noncomputable abbrev GreedyMersenneFatalAt := Erdos257PeriodNoncollapse.GreedyMersenneFatalAt
noncomputable abbrev weightedBoolSum :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.weightedBoolSum
noncomputable abbrev integerGreedyRemainder :=
  Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyRemainder
noncomputable abbrev localMersenneQuotient := Erdos257PeriodNoncollapse.localMersenneQuotient
noncomputable abbrev localPrefixQuotient := Erdos257PeriodNoncollapse.localPrefixQuotient
noncomputable abbrev endpointDivisorContribution :=
  Erdos257PeriodNoncollapse.endpointDivisorContribution
noncomputable abbrev localMersenneWeightsFrom :=
  Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeightsFrom
noncomputable abbrev localMersenneWeights :=
  Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.localMersenneWeights
noncomputable abbrev lowerSupportFromBits :=
  Erdos257PeriodNoncollapse.BooleanMobiusGreedyReduction.lowerSupportFromBits
noncomputable abbrev twentyOneQuotientTarget := Erdos257PeriodNoncollapse.twentyOneQuotientTarget
noncomputable abbrev rationalMersenneGreedyBitsFrom :=
  Erdos257PeriodNoncollapse.rationalMersenneGreedyBitsFrom
noncomputable abbrev twentyOneEvenQuotientGreedySupport :=
  Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedySupport
noncomputable abbrev twentyOneEvenQuotientGreedyRemainder :=
  Erdos257PeriodNoncollapse.twentyOneEvenQuotientGreedyRemainder
noncomputable abbrev localPrefixTwoStepPulse := Erdos257PeriodNoncollapse.localPrefixTwoStepPulse
noncomputable abbrev twentyOneTargetTwoStepPulse :=
  Erdos257PeriodNoncollapse.twentyOneTargetTwoStepPulse
noncomputable abbrev TwentyOneClosedLowerStateSupply :=
  Erdos257PeriodNoncollapse.TwentyOneClosedLowerStateSupply
noncomputable abbrev TwentyOneGreedyEventuallyHitsDoublingBlocks :=
  Erdos257PeriodNoncollapse.TwentyOneGreedyEventuallyHitsDoublingBlocks
noncomputable abbrev TwentyOneFatalAlignedBranch :=
  Erdos257PeriodNoncollapse.TwentyOneFatalAlignedBranch

lemma integerGreedyBits_fun_eq :
    integerGreedyBits =
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits := by
  funext weights C
  induction weights generalizing C with
  | nil =>
    simp [integerGreedyBits,
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits]
  | cons w ws ih =>
    simp [integerGreedyBits,
      Erdos257PeriodNoncollapse.HalfCylinderIntegerGreedy.integerGreedyBits, ih]

theorem twentyOneClosedRow_forces_quotientGreedy
    {R s : ℕ} {bits : List Bool}
    (hlen : bits.length = (localMersenneWeights (2 * R) R).length)
    (hrow :
      weightedBoolSum (localMersenneWeights (2 * R) R) bits + s =
        twentyOneQuotientTarget (2 * R))
    (hclosed : s ≤ 2 ^ R) :
    bits = integerGreedyBits
          (localMersenneWeights (2 * R) R)
          (twentyOneQuotientTarget (2 * R)) ∧
      s = twentyOneEvenQuotientGreedyRemainder R := by
  convert Erdos257PeriodNoncollapse.twentyOneClosedRow_forces_quotientGreedy
    hlen hrow hclosed
  all_goals try exact integerGreedyBits_fun_eq

theorem one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    (hsupply : TwentyOneClosedLowerStateSupply) :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet := by
  convert Erdos257PeriodNoncollapse.one_div_twenty_one_mem_mersenneAchievementSet_of_closedLowerStates
    hsupply
  all_goals try rfl

theorem one_div_twenty_one_mem_iff_not_fatalAlignedBranch :
    (1 / 21 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ TwentyOneFatalAlignedBranch := by
  convert Erdos257PeriodNoncollapse.one_div_twenty_one_mem_iff_not_fatalAlignedBranch
  all_goals try rfl

theorem twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      2 ^ R < twentyOneEvenQuotientGreedyRemainder R := by
  convert Erdos257PeriodNoncollapse.twentyOneFatalAlignedBranch_eventually_strict_supercapacity
    hbranch
  all_goals try rfl

theorem twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    (hbranch : TwentyOneFatalAlignedBranch) :
    ∃ K : ℕ, ∀ R : ℕ, K ≤ R →
      twentyOneEvenQuotientGreedySupport (R + 1) =
          insert (R + 1) (twentyOneEvenQuotientGreedySupport R) ∧
        twentyOneEvenQuotientGreedyRemainder (R + 1) =
          (4 * twentyOneEvenQuotientGreedyRemainder R +
              twentyOneTargetTwoStepPulse (2 * R) -
                localPrefixTwoStepPulse
                  (twentyOneEvenQuotientGreedySupport R) (2 * R)) -
            (2 ^ (R + 1) + 1) := by
  convert Erdos257PeriodNoncollapse.twentyOneFatalAlignedBranch_eventually_affine_supercapacity
    hbranch
  all_goals try rfl

end

end PalomarCorpus.E257.TwentyOneFatalBranch
