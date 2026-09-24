/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_35

Every non-theorem declaration of `PalomarCorpus/E257_35/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open ArithmeticFunction
open scoped ArithmeticFunction.Moebius

namespace PalomarCorpus.E257_35.Shared
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
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
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_35.Shared

namespace PalomarCorpus.E257.PaperStructuresAY
open scoped BigOperators
export PalomarCorpus.E257_35.Shared (localMersenneQuotient)
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
end PalomarCorpus.E257.PaperStructuresAY

namespace PalomarCorpus.E257.PaperStatementsAD
open scoped BigOperators
export PalomarCorpus.E257_35.Shared (localMersenneGeometricQuotient localMersenneQuotient)
end PalomarCorpus.E257.PaperStatementsAD

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
export PalomarCorpus.E257_35.Shared (localMersenneGeometricQuotient localMersenneQuotient)
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
end PalomarCorpus.E257.PaperStatementsAR

namespace PalomarCorpus.E257.PaperStatementsAE
open Filter
open Set
export PalomarCorpus.E257_35.Shared (IsTemperedBinaryOrbit binaryCoeffSeries binaryCoeffTail)
end PalomarCorpus.E257.PaperStatementsAE

namespace PalomarCorpus.E257.PaperStatementsAU
open ArithmeticFunction
open Filter
open Set
open scoped ArithmeticFunction.Moebius
open Topology
export PalomarCorpus.E257_35.Shared (IsTemperedBinaryOrbit binaryCoeffSeries erdosSupportSeries supportCoeff)
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
end PalomarCorpus.E257.PaperStatementsAU

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
export PalomarCorpus.E257_35.Shared (supportCoeff)
end PalomarCorpus.E257.PaperStatementsAG

namespace PalomarCorpus.E257.PaperStatementsAV
open ArithmeticFunction
open Filter
open Set
open Topology
export PalomarCorpus.E257_35.Shared (binaryCoeffTail erdosSupportSeries supportCoeff)
/-- The reciprocal summand of a support, with exponent zero harmlessly normalized to zero by real division. Local copy of Erdos249257.reciprocalSupportTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a
/-- The reciprocal mass `ρ(A) = ∑_{a∈A} 1/a`. Local copy of Erdos249257.reciprocalMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a
end PalomarCorpus.E257.PaperStatementsAV
