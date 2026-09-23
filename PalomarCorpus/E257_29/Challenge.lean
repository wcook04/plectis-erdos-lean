/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257: uniqueness for gap-dominated finite weights; a geometric form of the quotient condition; bounds for a general coefficient sequence

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace PalomarCorpus.E257_29.Shared
/-- The tempered binary carry orbit condition for an integer sequence u attached to a coefficient sequence c and a natural number v, with no positivity imposed on v: the exact recurrence u (N+1) = 2 u N minus v times c (N+1) holds for every N, and u N divided by 2 to the power N tends to 0. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The binary tail of a coefficient sequence c beyond scale N, namely the sum over j at least 0 of c at N+j+1 divided by 2 to the power j+1. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The quotient of one scaled Mersenne weight written without division: a shift by the Euclidean remainder times a finite geometric word. Local copy of Erdos249257.localMersenneGeometricQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneGeometricQuotient (M d : ℕ) : ℕ :=
  2 ^ (M % d) * ∑ j ∈ Finset.range (M / d), (2 ^ d) ^ j
/-- The local integer Mersenne quotient at binary scale M and rank d, namely the natural number quotient of 2 to the power M by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_29.Shared

namespace PalomarCorpus.E257.PaperStructuresAY
open scoped BigOperators
export PalomarCorpus.E257_29.Shared (localMersenneQuotient)
/-- Descending local quotient weights with ranks `d,d+1,…,R`. Local copy of Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneWeightsFrom (M R : ℕ) : ℕ → List ℕ
  | d =>
      if h : d ≤ R then
        localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1)
      else
        []
termination_by d => R + 1 - d
decreasing_by omega
/-- The complete lower quotient word on ranks `2,…,R`. Local copy of Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneWeights (M R : ℕ) : List ℕ :=
  localMersenneWeightsFrom M R 2
/-- Number of binary suffix values available after a truncation at depth `M`, when ranks through `R` have already been fixed. Local copy of Erdos249257.BooleanMobiusGreedyReduction.lowerBinaryWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lowerBinaryWindow (M R : ℕ) : ℕ :=
  2 ^ (M - R)
/-- Every head exceeds the sum of its complete tail by at least `gap`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.GapDominates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GapDominates (gap : ℕ) : List ℕ → Prop
  | [] => True
  | w :: ws => gap + ws.sum ≤ w ∧ GapDominates gap ws
/-- Descending greedy subset for an integer capacity. Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- Weighted sum of a Boolean word. The equal-length hypotheses below make the two fallback equations irrelevant. Local copy of Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
/-- States record:257bm-i11c from the long record for Erdős problem #257. Transported from Erdos249257.BooleanMobiusGreedyReduction.localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
        (2 ^ (M - 1) - 1) := by
  sorry
/-- States record:257bm-i11b from the long record for Erdős problem #257. Transported from Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localMersenneWeights_gapDominates_odd (R : ℕ) :
    GapDominates (2 ^ R) (localMersenneWeights (2 * R) R) := by
  sorry
end PalomarCorpus.E257.PaperStructuresAY

namespace PalomarCorpus.E257.PaperStatementsAD
open scoped BigOperators
export PalomarCorpus.E257_29.Shared (localMersenneGeometricQuotient localMersenneQuotient)
/-- States record:257bm-i12 from the long record for Erdős problem #257. Transported from Erdos249257.localMersenneQuotient_eq_geometric in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localMersenneQuotient_eq_geometric
    {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = localMersenneGeometricQuotient M d := by
  sorry
end PalomarCorpus.E257.PaperStatementsAD

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
export PalomarCorpus.E257_29.Shared (localMersenneGeometricQuotient localMersenneQuotient)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- The corresponding geometric normal form of a finite prefix quotient. Local copy of Erdos249257.localGeometricPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localGeometricPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneGeometricQuotient M d
/-- States record:257bm-i12 from the long record for Erdős problem #257. Transported from Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometric
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) ≤
        localGeometricPrefixQuotient (insert c D) (2 * c - 2) := by
  sorry
/-- States record:257bm-i12 from the long record for Erdős problem #257. Transported from Erdos249257.localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff_geometricCore
    {D : Finset ℕ} {c : ℕ}
    (hc : 4 ≤ c)
    (hD : ∀ d ∈ D, 2 ≤ d ∧ d < c)
    (hbelow : localMersennePrefixValue D < (1 / 2 : ℚ)) :
    localBinarySuffix D 1 (2 * c - 2) < 2 ^ (c - 2) ↔
      2 ^ ((2 * c - 2) - 1) - 2 ^ (c - 2) ≤
        localGeometricPrefixQuotient D (2 * c - 2) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAR

namespace PalomarCorpus.E257.PaperStatementsAE
open Filter
open Set
export PalomarCorpus.E257_29.Shared (IsTemperedBinaryOrbit binaryCoeffSeries binaryCoeffTail)
/-- States record:257bm-i2 from the long record for Erdős problem #257. Transported from Erdos249257.binaryCoeffTail_div_pow_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binaryCoeffTail_div_pow_tendsto_zero
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    Tendsto (fun N : ℕ ↦ binaryCoeffTail c N / (2 : ℝ) ^ N) atTop (nhds 0) := by
  sorry
/-- States record:257bm-i2 from the long record for Erdős problem #257. Transported from Erdos249257.binaryCoeffTail_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binaryCoeffTail_le (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N : ℕ) :
    binaryCoeffTail c N ≤ (N : ℝ) + 2 := by
  sorry
/-- States record:257bm-i-t7 from the long record for Erdős problem #257. Transported from Erdos249257.not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := by
  sorry
end PalomarCorpus.E257.PaperStatementsAE

namespace PalomarCorpus.E257.PaperStatementsAU
open ArithmeticFunction
open Filter
open Set
open scoped ArithmeticFunction.Moebius
open Topology
export PalomarCorpus.E257_29.Shared (IsTemperedBinaryOrbit binaryCoeffSeries erdosSupportSeries supportCoeff)
/-- A real number represented by an integer numerator and a positive natural denominator. This is the explicit positive-denominator form of membership in `ℚ`; it keeps the carry multiplier visible in theorem statements. Local copy of Erdos249257.HasRationalValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)
/-- The positive-index integer indicator of a support. Arithmetic functions must vanish at zero, which is also the correct normalization for the Lambert coefficient calculus. Local copy of Erdos249257.positiveSupportBit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveSupportBit (A : Set ℕ) (n : ℕ) : ℤ :=
  letI := Classical.propDecidable (0 < n ∧ n ∈ A)
  if 0 < n ∧ n ∈ A then 1 else 0
/-- `positiveSupportBit` packaged as an integer-valued arithmetic function. Local copy of Erdos249257.positiveSupportBitAF, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveSupportBitAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨positiveSupportBit A, by simp [positiveSupportBit]⟩
/-- The support divisor-count coefficient, cast to an integer-valued arithmetic function. Local copy of Erdos249257.supportCoeffAF, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeffAF (A : Set ℕ) : ArithmeticFunction ℤ :=
  ⟨fun n ↦ (supportCoeff A n : ℤ), by simp [supportCoeff]⟩
/-- States record:257bm-i-bridge from the long record for Erdős problem #257. Transported from Erdos249257.erdosSupportSeries_rational_iff_exists_temperedCarry in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdosSupportSeries_rational_iff_exists_temperedCarry (A : Set ℕ) :
    HasRationalValue (erdosSupportSeries 2 A) ↔
      ∃ q : ℕ, 0 < q ∧ ∃ U : ℕ → ℤ,
        IsTemperedBinaryOrbit (supportCoeff A) q U := by
  sorry
/-- States record:257bm-i-bridge from the long record for Erdős problem #257. Transported from Erdos249257.erdosSupportSeries_two_eq_binaryCoeffSeries in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem erdosSupportSeries_two_eq_binaryCoeffSeries (A : Set ℕ) :
    erdosSupportSeries 2 A = binaryCoeffSeries (supportCoeff A) := by
  sorry
/-- States record:257bm-i-mob from the long record for Erdős problem #257. Transported from Erdos249257.mobius_supportCoeff_boolean in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobius_supportCoeff_boolean (A : Set ℕ) (n : ℕ) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 0 ∨
      (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 := by
  sorry
/-- States record:257bm-i-mob from the long record for Erdős problem #257. Transported from Erdos249257.mobius_supportCoeff_eq_one_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mobius_supportCoeff_eq_one_iff (A : Set ℕ) {n : ℕ} (hn : 0 < n) :
    (ArithmeticFunction.moebius * supportCoeffAF A) n = 1 ↔ n ∈ A := by
  sorry
/-- States record:257bm-i-mob from the long record for Erdős problem #257. Transported from Erdos249257.moebius_mul_supportCoeffAF in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem moebius_mul_supportCoeffAF (A : Set ℕ) :
    ArithmeticFunction.moebius * supportCoeffAF A = positiveSupportBitAF A := by
  sorry
end PalomarCorpus.E257.PaperStatementsAU

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
export PalomarCorpus.E257_29.Shared (supportCoeff)
/-- States record:257bm-i-bridge from the long record for Erdős problem #257. Transported from Erdos249257.supportCoeff_le_card_divisors in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supportCoeff_le_card_divisors (A : Set ℕ) (n : ℕ) :
    supportCoeff A n ≤ n.divisors.card := by
  sorry
/-- States record:257bm-i-bridge from the long record for Erdős problem #257. Transported from Erdos249257.supportCoeff_le_self in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supportCoeff_le_self (A : Set ℕ) (n : ℕ) : supportCoeff A n ≤ n := by
  sorry
end PalomarCorpus.E257.PaperStatementsAG

namespace PalomarCorpus.E257.PaperStatementsAV
open ArithmeticFunction
open Filter
open Set
open Topology
export PalomarCorpus.E257_29.Shared (binaryCoeffTail erdosSupportSeries supportCoeff)
/-- The reciprocal summand of a support, with exponent zero harmlessly normalized to zero by real division. Local copy of Erdos249257.reciprocalSupportTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a
/-- The reciprocal mass `ρ(A) = ∑_{a∈A} 1/a`. Local copy of Erdos249257.reciprocalMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a
/-- States record:257rig-i2 from the long record for Erdős problem #257. Transported from Erdos249257.dyadic_support_fraction_reciprocalMass_diverges_or_gt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_support_fraction_reciprocalMass_diverges_or_gt_one
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c : ℕ)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    ¬ Summable (reciprocalSupportTerm A) ∨ 1 < reciprocalMass A := by
  sorry
/-- States record:257rig-i3 from the long record for Erdős problem #257. Transported from Erdos249257.exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_unbounded_shifted_odd_tail_nat_state_of_support_fraction
    (A : Set ℕ) (hAinf : A.Infinite) (p : ℤ) (c v : ℕ) (hv : 0 < v)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c * v : ℕ) : ℝ)) :
    ∃ u : ℕ → ℕ,
      (∀ n : ℕ, (u n : ℝ) =
        (v : ℝ) * binaryCoeffTail (supportCoeff A) (c + n)) ∧
      (∀ n : ℕ, 0 < u n) ∧
      (∀ n : ℕ, u (n + 1) +
        v * supportCoeff A (c + n + 1) = 2 * u n) ∧
      (∀ n : ℕ, u n ≡ p.toNat * 2 ^ n [MOD v]) ∧
      (∀ B : ℕ, ∃ n : ℕ, B < u n) := by
  sorry
/-- States record:257rig-i2 from the long record for Erdős problem #257. Transported from Erdos249257.one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_lt_reciprocalMass_of_dyadic_support_fraction_of_two_pos_mem
    (A : Set ℕ) (hsum : Summable (reciprocalSupportTerm A))
    (p : ℤ) (c : ℕ) {a b : ℕ}
    (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b)
    (haA : a ∈ A) (hbA : b ∈ A)
    (hvalue : erdosSupportSeries 2 A =
      (p : ℝ) / ((2 ^ c : ℕ) : ℝ)) :
    1 < reciprocalMass A := by
  sorry
end PalomarCorpus.E257.PaperStatementsAV
