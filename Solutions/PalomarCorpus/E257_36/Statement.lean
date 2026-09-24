/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_36

Every non-theorem declaration of `PalomarCorpus/E257_36/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open ArithmeticFunction
open Filter
open Set
open Topology
open scoped ArithmeticFunction.Omega
open scoped ENNReal
open MeasureTheory
open scoped BigOperators

namespace PalomarCorpus.E257_36.Shared
/-- The three-channel Lambert lower bound for the Mersenne tail `T (k + 1)`. `T (k + 1) = ∑_{v ≥ 1} 2 ^ (-k * v) / (2 ^ v - 1)`; truncating that expansion after `v = 3` gives this rational function of `t = 2 ^ k`, namely `1/t + 1/(3 * t ^ 2) + 1/(7 * t ^ 3)` (equivalently `1 / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k)`). Local copy of Erdos249257.HalfGreedyFatalGap.mersenneTailLB3, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTailLB3 (k : ℕ) : ℝ :=
  1 / 2 ^ k + 1 / (3 * (2 ^ k) ^ 2) + 1 / (7 * (2 ^ k) ^ 3)
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_36.Shared

namespace PalomarCorpus.E257.PaperStatementsAV
open ArithmeticFunction
open Filter
open Set
open Topology
export PalomarCorpus.E257_36.Shared (supportCoeff)
end PalomarCorpus.E257.PaperStatementsAV

namespace PalomarCorpus.E257.PaperStatementsAL
open Filter
open Set
open Topology
export PalomarCorpus.E257_36.Shared (supportCoeff)
/-- `f` vanishes at the `h` positive offsets after `N`, namely `N + 1, ..., N + h`. Local copy of Erdos249257.CoeffZeroWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CoeffZeroWindow (f : ℕ → ℕ) (N h : ℕ) : Prop :=
  ∀ j : ℕ, j < h → f (N + j + 1) = 0
/-- `supportCoeff A` vanishes on the `h` positive indices immediately after `N`, namely `N + 1, ..., N + h`. Local copy of Erdos249257.SupportCoeffZeroWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  CoeffZeroWindow (supportCoeff A) N h
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
end PalomarCorpus.E257.PaperStatementsAL

namespace PalomarCorpus.E257.PaperStatementsAF
open Set
/-- Completely explicit constant for the fixed-`k` divisor bound. Local copy of Erdos249257.divisorSubpowerConst, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def divisorSubpowerConst (k : ℕ) : ℕ := k ^ (2 ^ k)
end PalomarCorpus.E257.PaperStatementsAF

namespace PalomarCorpus.E257.PaperStatementsAO
open Filter
open Topology
open scoped ArithmeticFunction.Omega
export PalomarCorpus.E257_36.Shared (supportCoeff)
/-- The signed coefficient layer between exact `p`-adic levels `e-1` and `e`. Local copy of Erdos249257.MaximalOmegaLayer.primePowerLayer, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primePowerLayer (p e : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g (p ^ e * n) - g (p ^ (e - 1) * n)
/-- The two-signature mixed layer. Further list-level iteration can use this as its checked algebraic step without committing to a factorization API. Local copy of Erdos249257.MaximalOmegaLayer.mixedPrimePowerLayerTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mixedPrimePowerLayerTwo
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  primePowerLayer q f (primePowerLayer p e g) n
/-- Integer-valued packaging of the support divisor-count coefficient. Local copy of Erdos249257.SupportDilationDifferences.supportCoeffInt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeffInt (A : Set ℕ) (n : ℕ) : ℤ :=
  supportCoeff A n
end PalomarCorpus.E257.PaperStatementsAO

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
/-- The exact rational Mersenne weight `1 / (2^n - 1)`. Its meaningful support indices are positive; at index zero Lean's division convention gives zero. Local copy of Erdos249257.mersenneWeightRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
end PalomarCorpus.E257.PaperStatementsAR

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_36.Shared (mersenneTail mersenneWeight)
/-- The positive gap between one Mersenne weight and the tail after it. Local copy of Erdos249257.mersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsAA
export PalomarCorpus.E257_36.Shared (mersenneTailLB3)
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStructuresH
export PalomarCorpus.E257_36.Shared (mersenneTailLB3)
end PalomarCorpus.E257.PaperStructuresH

namespace PalomarCorpus.E257.PaperStructuresV
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_36.Shared (mersenneTail mersenneWeight)
end PalomarCorpus.E257.PaperStructuresV
