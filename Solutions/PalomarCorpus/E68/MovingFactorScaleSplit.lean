/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PrimeZeroBranch
import Solutions.PalomarCorpus.E68.Statement

open scoped BigOperators

namespace PalomarCorpus.E68.MovingFactorScaleSplit

noncomputable section

theorem movingPrivateFactorScaleSplit_implies_irrational
    (hcert :
      ∀ B : ℕ, ∃ m q : ℕ,
        4 ≤ m ∧
        B < m / 2 + 1 ∧
        q ∈ factorialGapLargePrefixPrivatePrimes m ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockEndpointLcm (m / 2 + 1) <
          factorialBlockScale (m / 2 + 1) *
            complementaryProjectedResidue
              (factorialBlockTailNumerator (m / 2 + 1))
              (factorialBlockPrivateModulus (m / 2 + 1)) ∧
        factorialBlockBudget (m / 2 + 1) *
              factorialBlockCollisionCore (m / 2 + 1) * q <
          factorialBlockScale (m / 2 + 1)) :
    Irrational factorialGapSeries := by
  have hsource :
      Irrational _root_.Erdos68.factorialGapSeries :=
    ErdosProblems.Erdos68.irrational_factorialGapSeries_of_cofinal_largePrefixPrivate_unitScaleSplit
      (by
        simpa [factorialGapLargePrefixPrivatePrimes,
          factorialBlockIndices, factorialGapDenominator, factorialBlockBase,
          pairwiseCollisionCore, collisionCore, endpointDenominatorLcm,
          endpointTailNumerator, privateQuotient, privateModulus,
          projectedResidue, complementaryProjectedResidue,
          factorialBlockEndpointLcm, factorialBlockCollisionCore,
          factorialBlockPrivateModulus, factorialBlockTailNumerator,
          factorialBlockScale, factorialBlockBudget,
          ErdosProblems.Erdos68.factorialGapLargePrefixPrivatePrimes,
          ErdosProblems.Erdos68.factorialBlockIndices,
          ErdosProblems.Erdos68.factorialGapDenominator,
          ErdosProblems.Erdos68.factorialBlockBase,
          ErdosProblems.Erdos68.pairwiseCollisionCore,
          ErdosProblems.Erdos68.collisionCore,
          ErdosProblems.Erdos68.endpointDenominatorLcm,
          ErdosProblems.Erdos68.endpointTailNumerator,
          ErdosProblems.Erdos68.privateQuotient,
          ErdosProblems.Erdos68.privateModulus,
          ErdosProblems.Erdos68.projectedResidue,
          ErdosProblems.Erdos68.complementaryProjectedResidue,
          ErdosProblems.Erdos68.factorialBlockEndpointLcm,
          ErdosProblems.Erdos68.factorialBlockCollisionCore,
          ErdosProblems.Erdos68.factorialBlockPrivateModulus,
          ErdosProblems.Erdos68.factorialBlockTailNumerator,
          ErdosProblems.Erdos68.factorialBlockScale,
          ErdosProblems.Erdos68.factorialBlockBudget] using hcert)
  simpa [factorialGapSeries, _root_.Erdos68.factorialGapSeries,
    _root_.Erdos68.factorialGapTail,
    _root_.Erdos68.factorialGapTailTerm] using hsource

theorem splitFactorNormalizedCollision_implies_irrational
    (hcert :
      ∀ B : ℕ, ∃ p a b : ℕ,
        p.Prime ∧
        B < p ∧
        a ∣ factorialBlockPrivateModulus p ∧
        b ∣ factorialBlockPrivateModulus p ∧
        1 < factorialBlockPrivateModulus p ∧
        complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p a) ≠
          complementaryProjectedResidue
            (factorialBlockTailNumerator p)
            (factorialBlockFactorProjectionModulus p b) ∧
        factorialBlockBudget p *
              factorialBlockNormalizedCollisionCore p * max a b <
          2 * p ^ 2 * factorialBlockUpperDescFactorial p) :
    Irrational factorialGapSeries := by
  have hsource :
      Irrational _root_.Erdos68.factorialGapSeries :=
    ErdosProblems.Erdos68.irrational_factorialGapSeries_of_cofinal_complementary_factor_disagreement_normalizedCollisionCap
      (by
        simpa [factorialBlockIndices, factorialGapDenominator,
          factorialBlockBase, pairwiseCollisionCore, collisionCore,
          endpointDenominatorLcm, endpointTailNumerator, privateQuotient,
          privateModulus, projectedResidue, complementaryProjectedResidue,
          leaveOneOutModulus, factorialBlockCollisionCore,
          factorialBlockNormalizedCollisionCore,
          factorialBlockUpperDescFactorial, factorialBlockPrivateModulus,
          factorialBlockTailNumerator, factorialBlockFactorProjectionModulus,
          factorialBlockBudget,
          ErdosProblems.Erdos68.factorialBlockIndices,
          ErdosProblems.Erdos68.factorialGapDenominator,
          ErdosProblems.Erdos68.factorialBlockBase,
          ErdosProblems.Erdos68.pairwiseCollisionCore,
          ErdosProblems.Erdos68.collisionCore,
          ErdosProblems.Erdos68.endpointDenominatorLcm,
          ErdosProblems.Erdos68.endpointTailNumerator,
          ErdosProblems.Erdos68.privateQuotient,
          ErdosProblems.Erdos68.privateModulus,
          ErdosProblems.Erdos68.projectedResidue,
          ErdosProblems.Erdos68.complementaryProjectedResidue,
          ErdosProblems.Erdos68.leaveOneOutModulus,
          ErdosProblems.Erdos68.factorialBlockCollisionCore,
          ErdosProblems.Erdos68.factorialBlockNormalizedCollisionCore,
          ErdosProblems.Erdos68.factorialBlockUpperDescFactorial,
          ErdosProblems.Erdos68.factorialBlockPrivateModulus,
          ErdosProblems.Erdos68.factorialBlockTailNumerator,
          ErdosProblems.Erdos68.factorialBlockFactorProjectionModulus,
          ErdosProblems.Erdos68.factorialBlockBudget] using hcert)
  simpa [factorialGapSeries, _root_.Erdos68.factorialGapSeries,
    _root_.Erdos68.factorialGapTail,
    _root_.Erdos68.factorialGapTailTerm] using hsource

theorem fixedOwnerPair_eventually_absorbed
    {p i j : ℕ}
    (hi : 2 ≤ i)
    (hj : 2 ≤ j)
    (hlt :
      max (factorialGapDenominator i)
          (factorialGapDenominator j) < p) :
    factorialBlockPrivateQuotient p i = 1 ∧
      factorialBlockPrivateQuotient p j = 1 := by
  simpa [factorialBlockIndices, factorialGapDenominator,
    factorialBlockBase, pairwiseCollisionCore, collisionCore,
    privateQuotient, factorialBlockPrivateQuotient,
    ErdosProblems.Erdos68.factorialBlockIndices,
    ErdosProblems.Erdos68.factorialGapDenominator,
    ErdosProblems.Erdos68.factorialBlockBase,
    ErdosProblems.Erdos68.pairwiseCollisionCore,
    ErdosProblems.Erdos68.collisionCore,
    ErdosProblems.Erdos68.privateQuotient,
    ErdosProblems.Erdos68.factorialBlockPrivateQuotient] using
      ErdosProblems.Erdos68.factorialBlockFixedPairPrivateQuotients_eq_one
        hi hj hlt

end

end PalomarCorpus.E68.MovingFactorScaleSplit
