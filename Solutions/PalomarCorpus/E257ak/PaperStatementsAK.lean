/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusExactTransition
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences
import ErdosProblems.Erdos257.PaperCompleteR21.UpperResetBandCertificate
import Solutions.PalomarCorpus.E257ak.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAK

theorem localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq
    {M R A : ℕ} {bits : List Bool}
    (hRM : R ≤ M)
    (hlen : bits.length = (localMersenneWeights M R).length)
    (hfill :
      weightedBoolSum (localMersenneWeights M R) bits + A =
        2 ^ (M - 1) - 1)
    (hA : A < lowerBinaryWindow M R) :
    bits = integerGreedyBits (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) ∧
      A = integerGreedyRemainder (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) := @Erdos249257.BooleanMobiusGreedyReduction.localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq M R A bits hRM hlen hfill hA

theorem localMersenneWeightsFrom_gapDominates
    {M R d : ℕ} (hRM : R ≤ M) (hd : 1 ≤ d) :
    GapDominates (lowerBinaryWindow M R)
      (localMersenneWeightsFrom M R d) := @Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom_gapDominates M R d hRM hd

theorem localMersenneWeights_gapDominates_even
    (R : ℕ) (hR : 1 ≤ R) :
    GapDominates (2 ^ (R - 1)) (localMersenneWeights (2 * R - 1) R) := @Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_even R hR

theorem localMersenneWeights_gapDominates_odd (R : ℕ) :
    GapDominates (2 ^ R) (localMersenneWeights (2 * R) R) := @Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_odd R

theorem remainder_lt_gap_iff_eq_integerGreedyBits
    {gap C : ℕ} {weights : List ℕ} {bits : List Bool} (hgap : 0 < gap)
    (hdom : GapDominates gap weights)
    (hlen : bits.length = weights.length)
    (hadm : weightedBoolSum weights bits ≤ C) :
    C - weightedBoolSum weights bits < gap ↔
      bits = integerGreedyBits weights C ∧
        integerGreedyRemainder weights C < gap := @Erdos249257.BooleanMobiusGreedyReduction.remainder_lt_gap_iff_eq_integerGreedyBits gap C weights bits hgap hdom hlen hadm

theorem paper_floor_quotient_geometric_sum {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = ∑ j ∈ Finset.Icc 1 (M / d), 2 ^ (M - j * d) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_floor_quotient_geometric_sum M d hd

theorem paper_next_floor_quotient {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient (M + 1) d =
      2 * localMersenneQuotient M d + (if d ∣ M + 1 then 1 else 0) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient M d hd

theorem paper_next_floor_quotient_no_fixed_point {M d : ℕ} (hd : 2 ≤ d)
    (hfix : localMersenneQuotient (M + 1) d = localMersenneQuotient M d) :
    localMersenneQuotient M d = 0 ∧ localMersenneQuotient (M + 1) d = 0 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient_no_fixed_point M d hd hfix

theorem paper_next_quotient_sum {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M + endpointDivisorContribution D (M + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_next_quotient_sum D M hD

theorem paper_repair_integer_eq_endpoint_defect {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hbelow : localPrefixQuotient D M ≤ halfEndpointTarget M) :
    localRepairInteger D 1 (M + 1) = localEndpointDefect D (M + 1) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_repair_integer_eq_endpoint_defect D M hM hD hbelow

theorem paper_signed_endpoint_defect_succ {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    localEndpointDefect D (M + 1) =
      2 * localEndpointDefect D M + 1 -
        (endpointDivisorContribution D (M + 1) : ℤ) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_defect_succ D M hM hD

theorem paper_signed_endpoint_recurrence (D : Finset ℕ) (k n : ℕ) :
    localRepairInteger D k n =
      2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
        (endpointDivisorContribution D n : ℤ) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_recurrence D k n

theorem paper_successor_remainders_fourteen_through_thirtyone :
    seamIntegerGreedyRemainder 14 = 392 ∧
      seamIntegerGreedyRemainder 15 = 34333 ∧
      seamIntegerGreedyRemainder 16 = 71791 ∧
      seamIntegerGreedyRemainder 17 = 156085 ∧
      seamIntegerGreedyRemainder 18 = 362187 ∧
      seamIntegerGreedyRemainder 19 = 924455 ∧
      seamIntegerGreedyRemainder 20 = 549353 ∧
      seamIntegerGreedyRemainder 21 = 100251 ∧
      seamIntegerGreedyRemainder 22 = 4595307 ∧
      seamIntegerGreedyRemainder 23 = 9992613 ∧
      seamIntegerGreedyRemainder 24 = 23193229 ∧
      seamIntegerGreedyRemainder 25 = 59218477 ∧
      seamIntegerGreedyRemainder 26 = 35546625 ∧
      seamIntegerGreedyRemainder 27 = 7968765 ∧
      seamIntegerGreedyRemainder 28 = 300310513 ∧
      seamIntegerGreedyRemainder 29 = 664371133 ∧
      seamIntegerGreedyRemainder 30 = 1583742700 ∧
      seamIntegerGreedyRemainder 31 = 4187487147 := @ErdosProblems.Erdos257.PaperCompleteR21.paper_successor_remainders_fourteen_through_thirtyone

end PalomarCorpus.E257.PaperStatementsAK
