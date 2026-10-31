/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_01

Every non-theorem declaration of `PalomarCorpus/E257_01/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set
open Filter Topology
open scoped BigOperators
open Finset
open Filter
open Topology

namespace PalomarCorpus.E257_01.Shared
/-- Data for a positive fractional divisor cover: a sequence of finite frames of positive integers (frame j, with 0 not in it), exponents alpha j with 0 < alpha j and alpha j at most 1, and nonnegative coefficients c j d with each column sum over d of c j d / d convergent, subject to the divisor majorisation that for every frame index j and every n at least 1 the number of members of frame j dividing n, raised to the power alpha j, is at most the sum of c j d over the divisors d of n. -/
structure PositiveCoverData where
  frame : ℕ → Finset ℕ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
noncomputable def PositiveCoverData.cost (C : PositiveCoverData) (j : ℕ) : ℝ :=
  ∑' d : ℕ, C.coefficient j d / (d : ℝ)
noncomputable def PositiveCoverData.StrengthenedCostSummable (C : PositiveCoverData) : Prop :=
  Summable (fun j : ℕ =>
    C.cost j * (2 : ℝ) ^ (((j + 1 : ℕ) : ℝ) * C.exponent j) /
      ((2 : ℝ) ^ C.exponent j - 1))
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
noncomputable def PositiveCoverData.host (C : PositiveCoverData) : Set ℕ :=
  {a | ∃ j, a ∈ C.frame j}
/-- The P part of a, namely the product over the primes p in the finite set P of p raised to the exponent of p in the factorisation of a. -/
noncomputable def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p
/-- The weighted term attached to an exponent a at base b, namely the P part of a divided by the product of a and b raised to the P part of a minus 1. -/
noncomputable def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))
/-- The finite prime part weighted hypothesis at base b: there is a finite nonempty set P of primes for which the weighted terms of A, that is the P part of a divided by a times b raised to the P part of a minus 1, form a summable family. This names the hypothesis, not any irrationality conclusion. -/
noncomputable def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))
end PalomarCorpus.E257_01.Shared

namespace PalomarCorpus.E257.DivisibilityWeightedSupport
open Set
export PalomarCorpus.E257_01.Shared (FinitePrimeWeighted erdosSupportSeries primeSetPart primeWeightedTerm)
/-- The divisibility weighted claim, named as a proposition with two clauses: first, for every integer base b at least 2 and every infinite A not containing 0 with finite prime part weighted mass at base b, the base b support series of A is irrational; second, for every host H not containing 0 with finite prime part weighted mass at base 2, every infinite subset of H has irrational support series at every integer base at least 2. -/
noncomputable def DivisibilityWeightedClaim : Prop :=
  (∀ (b : ℕ) (A : Set ℕ), 2 ≤ b → 0 ∉ A → A.Infinite →
    FinitePrimeWeighted b A → Irrational (erdosSupportSeries b A)) ∧
  (∀ H : Set ℕ, 0 ∉ H → FinitePrimeWeighted 2 H →
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A))
end PalomarCorpus.E257.DivisibilityWeightedSupport

namespace PalomarCorpus.E257.WeightedCloseReturn
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E257_01.Shared (FinitePrimeWeighted erdosSupportSeries primeSetPart primeWeightedTerm)
/-- For a positive divisor d, the radix atom b^(N mod d)/(b^d − 1); defined to be zero at d = 0. -/
noncomputable def shiftedRadixAtom (b N d : ℕ) : ℝ :=
  if d = 0 then 0
  else (b : ℝ) ^ (N % d) / ((b : ℝ) ^ d - 1)
/-- The shifted radix atom restricted by the indicator of the support A. -/
noncomputable def shiftedRadixSupportAtom
    (b : ℕ) (A : Set ℕ) (N d : ℕ) : ℝ :=
  Set.indicator A (shiftedRadixAtom b N) d
/-- The shifted support-atom sum minus the original support series. -/
noncomputable def displacement (b : ℕ) (A : Set ℕ) (N : ℕ) : ℝ :=
  (∑' d : ℕ, shiftedRadixSupportAtom b A N d) - erdosSupportSeries b A
end PalomarCorpus.E257.WeightedCloseReturn

namespace PalomarCorpus.E257.VariableExponentCover
open Set
export PalomarCorpus.E257_01.Shared (PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host)
/-- The strengthened positive cover claim, named as a proposition: for every positive cover datum satisfying the strengthened one inverse power cost condition, every infinite subset of its host has irrational support series at every integer base at least 2. -/
noncomputable def StrengthenedPositiveCoverClaim : Prop :=
  ∀ C : PositiveCoverData, C.StrengthenedCostSummable →
    ∀ A : Set ℕ, A ⊆ C.host → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
end PalomarCorpus.E257.VariableExponentCover

namespace PalomarCorpus.E257.MixedWeightedCover
open Set
export PalomarCorpus.E257_01.Shared (FinitePrimeWeighted PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host primeSetPart primeWeightedTerm)
/-- A set A of exponents has a strengthened positive cover when some positive cover data has A inside its host and satisfies the strengthened one inverse power cost condition. -/
noncomputable def HasStrengthenedPositiveCover (A : Set ℕ) : Prop :=
  ∃ C : PositiveCoverData, A ⊆ C.host ∧ C.StrengthenedCostSummable
/-- The mixed support claim, named as a proposition: for every set E with 0 not in E and finite prime part weighted mass at base 2, and every set V admitting a strengthened positive cover, every infinite subset of the union of E and V has irrational support series at every integer base at least 2. -/
noncomputable def MixedSupportClaim : Prop :=
  ∀ E V : Set ℕ, 0 ∉ E → FinitePrimeWeighted 2 E →
    HasStrengthenedPositiveCover V →
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
end PalomarCorpus.E257.MixedWeightedCover

namespace PalomarCorpus.E257.PaperStructuresBO
open Finset
open Filter
open Topology
export PalomarCorpus.E257_01.Shared (FinitePrimeWeighted erdosSupportSeries primeSetPart primeWeightedTerm)
/-- The paper's arbitrary-weight positive-cover data on an actual support. Local copy of ErdosProblems.Erdos257.PaperCompleteR8.LogBudgetCover, restated so the compared statements elaborate against Mathlib alone. -/
structure LogBudgetCover (A : Set ℕ) where
  frame : ℕ → Finset ℕ
  weight : ℕ → ℝ
  exponent : ℕ → ℝ
  coefficient : ℕ → ℕ → ℝ
  frame_positive : ∀ j, 0 ∉ frame j
  weight_positive : ∀ j, 0 < weight j
  weight_sum : HasSum weight 1
  exponent_bounds : ∀ j, 0 < exponent j ∧ exponent j ≤ 1
  coefficient_nonneg : ∀ j d, 0 < d → 0 ≤ coefficient j d
  column_summable : ∀ j, Summable (fun d : ℕ => coefficient j d / (d : ℝ))
  covers : ∀ a ∈ A, ∃ j, a ∈ frame j
  majorises : ∀ j n, 0 < n →
    (((frame j).filter (fun a => a ∣ n)).card : ℝ) ^ exponent j ≤
      ∑ d ∈ n.divisors, coefficient j d
  budget_summable : Summable (fun j =>
    (∑' d : ℕ, coefficient j d / (d : ℝ)) /
      (weight j ^ exponent j) / ((2 : ℝ) ^ exponent j - 1))
end PalomarCorpus.E257.PaperStructuresBO
