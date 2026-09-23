/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_21

Every non-theorem declaration of `PalomarCorpus/E257_21/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
open scoped ArithmeticFunction.Omega

namespace PalomarCorpus.E257_21.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- For a displayed residual `p / (2L)`, the integer numerator of its excess above the next dyadic point `2^-(n+1)`. Indeed, `p/(2L) - 2^-(n+1) = E/(2^(n+1)L)`. Keeping `E` integral makes the unresolved skipped-branch comparison an exact Diophantine inequality rather than a real-valued phase estimate. Local copy of Erdos249257.nextDyadicExcessIntNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)
/-- The signed coefficient layer between exact `p`-adic levels `e-1` and `e`. Local copy of Erdos249257.MaximalOmegaLayer.primePowerLayer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primePowerLayer (p e : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g (p ^ e * n) - g (p ^ (e - 1) * n)
end PalomarCorpus.E257_21.Shared

namespace PalomarCorpus.E257.PaperStatementsAE
open Filter
open Set
/-- A real number represented by an integer numerator and a positive natural denominator. This is the explicit positive-denominator form of membership in `ℚ`; it keeps the carry multiplier visible in theorem statements. Local copy of Erdos249257.HasRationalValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
end PalomarCorpus.E257.PaperStatementsAE

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
end PalomarCorpus.E257.PaperStatementsAG

namespace PalomarCorpus.E257.PaperStatementsAF
open Set
export PalomarCorpus.E257_21.Shared (nextDyadicExcessIntNumerator)
/-- Numerator left after subtracting a reduced finite prefix `r / D` from a dyadic rational `p / 2^c`. The transport theorem below assumes the subtraction is nonnegative, so natural subtraction is exact. Local copy of Erdos249257.dyadicResidualNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicResidualNumerator (p r c D : ℕ) : ℕ :=
  p * D - 2 ^ c * r
/-- The displayed residual rational before its remaining power-of-two cancellation is normalized by `Rat`. Local copy of Erdos249257.dyadicResidualRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicResidualRat (p r c D : ℕ) : ℚ :=
  (dyadicResidualNumerator p r c D : ℚ) / (2 ^ c * D : ℕ)
end PalomarCorpus.E257.PaperStatementsAF

namespace PalomarCorpus.E257.PaperStatementsD
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_21.Shared (mersenneWeight nextDyadicExcessIntNumerator)
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- Exact rational version of the greedy residual. Local copy of Erdos249257.greedyMersenneRemainderRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The finite Erdős partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)` as a rational number, stated with subtraction in `ℚ` so the statement reads exactly like the mathematical series. Local copy of Erdos249257.finiteErdosSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)
/-- Positive exponents selected through a finite exact-rational greedy run. Local copy of Erdos249257.greedyMersennePrefixRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)
/-- The first geometric channel of the Mersenne tail. Local copy of Erdos249257.halfDyadicCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
/-- The exact finite greedy prefix used to display the half residual. Local copy of Erdos249257.halfGreedyPrefixRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyPrefixRat (n : ℕ) : ℚ :=
  finiteErdosSum (greedyMersennePrefixRat (1 / 2 : ℚ) n) 2
/-- The inherited odd denominator of the exact finite greedy prefix. Local copy of Erdos249257.halfGreedyPrefixDenominator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyPrefixDenominator (n : ℕ) : ℕ :=
  (halfGreedyPrefixRat n).den
/-- Displayed numerator `p_n` in `r_n = p_n / (2 * halfGreedyPrefixDenominator n)`. Local copy of Erdos249257.halfGreedyResidualDisplayedNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyResidualDisplayedNumerator (n : ℕ) : ℤ :=
  (halfGreedyPrefixDenominator n : ℤ) -
    2 * (halfGreedyPrefixRat n).num
/-- The actual greedy half-orbit specialization of the integral excess numerator. At level `n`, it measures excess above `2^-(n+1)`. Local copy of Erdos249257.halfGreedyNextDyadicExcessNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyNextDyadicExcessNumerator (n : ℕ) : ℤ :=
  nextDyadicExcessIntNumerator
    (halfGreedyResidualDisplayedNumerator n) n
    (halfGreedyPrefixDenominator n)
end PalomarCorpus.E257.PaperStatementsD

namespace PalomarCorpus.E257.PaperStatementsAA
export PalomarCorpus.E257_21.Shared (primePowerLayer)
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAO
open Filter
open Topology
open scoped ArithmeticFunction.Omega
export PalomarCorpus.E257_21.Shared (primePowerLayer)
/-- The two-signature mixed layer. Further list-level iteration can use this as its checked algebraic step without committing to a factorization API. Local copy of Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mixedPrimePowerLayerTwo
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  primePowerLayer q f (primePowerLayer p e g) n
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- Integer-valued packaging of the support divisor-count coefficient. Local copy of Erdos249257.SupportDilationDifferences.supportCoeffInt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeffInt (A : Set ℕ) (n : ℕ) : ℤ :=
  supportCoeff A n
/-- Support elements with exact `p`-adic exponent `e`, after removing the prime-power layer. Local copy of Erdos249257.SupportSunflowerDichotomy.exactPrimePowerPullback, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def exactPrimePowerPullback (p e : ℕ) (A : Set ℕ) : Set ℕ :=
  {d | d.Coprime p ∧ p ^ e * d ∈ A}
end PalomarCorpus.E257.PaperStatementsAO

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_21.Shared (mersenneWeight)
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- A finite half-gap witness in the cut-locator coordinates. Local copy of Erdos249257.ExistsFatalHalfGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExistsFatalHalfGap : Prop :=
  ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
      < 1 / 2 ∧
    (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
      + mersenneWeight (d + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- One term of the binary coding of the achievement set. Local copy of Erdos249257.mersenneDigitTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)
/-- The support value coded by a binary sequence. Local copy of Erdos249257.positiveMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b
end PalomarCorpus.E257.PaperStatementsAM
