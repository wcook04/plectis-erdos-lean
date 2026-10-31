/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record sections 1.2 to 1.5: a weighted condition on the support; positive divisor majorants; combining the two support criteria

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
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
/-- Both clauses of the divisibility weighted claim hold: finite prime part weighted mass at a fixed base b at least 2 on an infinite support avoiding 0 forces irrationality at that base, and finite prime part weighted mass at base 2 on a host avoiding 0 forces irrationality at every integer base at least 2 for every infinite subset of that host. The weighted hypothesis is strictly weaker than summability of the reciprocals of the support, and LiteralWeightedCover.exists_weighted_not_strengthened_host exhibits a weighted host of divergent reciprocal mass. This covers a proper class of supports and does not decide an arbitrary infinite support. -/
theorem divisibilityWeightedClaim : DivisibilityWeightedClaim := by
  sorry
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
/-- An infinite positive support satisfying the finite-prime weighted condition has strictly positive displacements below every ε > 0 at arbitrarily large indices, for every base b ≥ 2. -/
theorem weighted_displacement_cofinal_close_return
    (b : ℕ) (E : Set ℕ) (hb : 2 ≤ b) (hE0 : 0 ∉ E)
    (hE : FinitePrimeWeighted b E) (hInf : E.Infinite)
    (ε : ℝ) (hε : 0 < ε) (N : ℕ) :
    ∃ m : ℕ, N ≤ m ∧ 0 < displacement b E m ∧ displacement b E m < ε := by
  sorry
end PalomarCorpus.E257.WeightedCloseReturn

namespace PalomarCorpus.E257.VariableExponentCover
open Set
export PalomarCorpus.E257_01.Shared (PositiveCoverData PositiveCoverData.StrengthenedCostSummable PositiveCoverData.cost erdosSupportSeries PositiveCoverData.host)
/-- The strengthened positive cover claim, named as a proposition: for every positive cover datum satisfying the strengthened one inverse power cost condition, every infinite subset of its host has irrational support series at every integer base at least 2. -/
noncomputable def StrengthenedPositiveCoverClaim : Prop :=
  ∀ C : PositiveCoverData, C.StrengthenedCostSummable →
    ∀ A : Set ℕ, A ⊆ C.host → A.Infinite →
      ∀ b : ℕ, 2 ≤ b → Irrational (erdosSupportSeries b A)
/-- The strengthened positive cover claim holds: a positive fractional divisor cover with variable exponents that are positive and at most 1, nonnegative coefficients, convergent columns, divisor majorisation, and convergent one inverse power cost forces irrationality at every integer base at least 2 for every infinite subset of its host. This covers a proper class of supports and does not decide an arbitrary infinite support. -/
theorem strengthenedPositiveCoverClaim : StrengthenedPositiveCoverClaim := by
  sorry
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
/-- The mixed support claim holds: a finite prime part weighted host at base 2 avoiding 0 and a strengthened positive cover host together force irrationality at every integer base at least 2 for every infinite subset of their union. The two criteria are combined on one common observation scale, and no individual irrationality premise is assumed. This covers a proper class of supports and does not decide an arbitrary infinite support. -/
theorem mixedSupportClaim : MixedSupportClaim := by
  sorry
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
/-- States res:mixed-supports, thm:257-mixed-supports from the long record and the short record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR8.arbitraryWeightMixedSupport_allBase_hereditary in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem arbitraryWeightMixedSupport_allBase_hereditary
    (E V : Set ℕ) (hE0 : 0 ∉ E) (hE : FinitePrimeWeighted 2 E)
    (D : LogBudgetCover V) :
    ∀ A : Set ℕ, A ⊆ E ∪ V → A.Infinite → ∀ b : ℕ, 2 ≤ b →
      Irrational (erdosSupportSeries b A) := by
  sorry
end PalomarCorpus.E257.PaperStructuresBO
