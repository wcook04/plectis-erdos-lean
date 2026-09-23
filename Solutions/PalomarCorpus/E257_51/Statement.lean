/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_51

Every non-theorem declaration of `PalomarCorpus/E257_51/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Set
open Filter Set
open Filter Topology
open scoped BigOperators

namespace PalomarCorpus.E257_51.Shared
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
end PalomarCorpus.E257_51.Shared

namespace PalomarCorpus.E257.RationalMembership
open Set
export PalomarCorpus.E257_51.Shared (greedyMersenneRemainder mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
/-- The set of ranks selected by the greedy Mersenne rule on x, namely the positive m for which the weight at m is at most the greedy remainder after rank m minus 1. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The set of positive ranks that the greedy Mersenne rule on x does not select. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
end PalomarCorpus.E257.RationalMembership

namespace PalomarCorpus.E257.RationalTailRigidity
open Filter Set
export PalomarCorpus.E257_51.Shared (erdosSupportSeries supportCoeff)
/-- A zero window of length h beginning after N for a natural coefficient sequence f: f vanishes at N+j+1 for every j below h. -/
noncomputable def CoeffZeroWindow (f : ℕ → ℕ) (N h : ℕ) : Prop :=
  ∀ j : ℕ, j < h → f (N + j + 1) = 0
/-- A zero window of length h beginning after N for the divisor incidence coefficients of A, that is a stretch of h consecutive integers after N none of which has a divisor in A. -/
noncomputable def SupportCoeffZeroWindow (A : Set ℕ) (N h : ℕ) : Prop :=
  CoeffZeroWindow (supportCoeff A) N h
/-- The reciprocal support summand at a, namely 1 divided by a when a lies in A and 0 otherwise; the exponent a = 0 contributes 0. -/
noncomputable def reciprocalSupportTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a
/-- The reciprocal mass of A, namely the sum over a in A of 1 divided by a, taken as an unconditional sum of the reciprocal support terms. -/
noncomputable def reciprocalMass (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, reciprocalSupportTerm A a
/-- The multiplicative order of 2 modulo an odd positive integer v, formed from the unit that the oddness of v determines. -/
noncomputable def oddDoublingOrder (v : ℕ) (hvodd : Odd v) : ℕ :=
  orderOf (ZMod.unitOfCoprime 2 (Nat.coprime_two_left.mpr hvodd))
end PalomarCorpus.E257.RationalTailRigidity

namespace PalomarCorpus.E257.ReciprocalSupport
/-- The reciprocal support summand at a, namely 1 divided by a when a lies in A and 0 otherwise; the exponent a = 0 contributes 0. -/
noncomputable def supportReciprocalTerm (A : Set ℕ) (a : ℕ) : ℝ :=
  Set.indicator A (fun a : ℕ => (1 : ℝ) / (a : ℝ)) a
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0. -/
noncomputable def supportPowerSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a : ℕ => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
end PalomarCorpus.E257.ReciprocalSupport

namespace PalomarCorpus.E257.ScaledGreedyTrap
open Set
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E257_51.Shared (greedyMersenneRemainder mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
/-- The greedy remainder of x at scale N rescaled by the binary place value, namely 2 to the power N times the greedy Mersenne remainder of x after rank N. -/
noncomputable def scaledGreedyRemainder (x : ℝ) (N : ℕ) : ℝ :=
  (2 : ℝ) ^ N * greedyMersenneRemainder x N
/-- The rescaled Mersenne weight at rank n, namely 2 to the power n divided by 2 to the power n minus 1; at n = 0 the value is 0. -/
noncomputable def mersenneScale (n : ℕ) : ℝ :=
  (2 : ℝ) ^ n * mersenneWeight n
/-- The cofinal lower branch condition for x, named as a proposition: for every K there is an N at least K at which twice the scaled greedy remainder of x at N is strictly below the rescaled Mersenne weight at N+1. -/
noncomputable def ScaledGreedyLowerBranchCofinally (x : ℝ) : Prop :=
  ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
    2 * scaledGreedyRemainder x N < mersenneScale (N + 1)
/-- The cofinal boundedness condition for x, named as a proposition: there is a real bound B such that for every K some N at least K has scaled greedy remainder at most B. No global bound on the orbit is required. -/
noncomputable def ScaledGreedyRemainderCofinallyBounded (x : ℝ) : Prop :=
  ∃ B : ℝ, ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧ scaledGreedyRemainder x N ≤ B
end PalomarCorpus.E257.ScaledGreedyTrap

namespace PalomarCorpus.E257.TerminalScaledVanishing
open Filter Set
export PalomarCorpus.E257_51.Shared (erdosSupportSeries supportCoeff)
/-- The binary affine orbit driven by an integer sequence a from an initial value, defined by orbit 0 equal to the initial value and orbit (n+1) equal to twice orbit n minus a at n+1. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- The integer half carry attached to a support A, namely the binary affine orbit started at 1 and driven by the divisor incidence coefficients of A shifted by one, so that the orbit at n+1 is twice the orbit at n minus the number of divisors of n+2 lying in A; the shift and the recursion index compose, so the coefficient consumed at step n+1 is the one at n+2. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- A Boolean support word through depth N, that is a Boolean valued function on the ranks 0 up to N. -/
noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool
/-- The set of ranks represented by a finite Boolean word, namely the ranks below its depth plus one at which the word is true. -/
noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}
/-- The terminal scaled vanishing hypothesis packaged as a structure: a sequence of depths and of Boolean support words at those depths, with every depth at least 1, depths tending to infinity, ranks 0 and 1 excluded from every word, and the absolute integer half carry of the word evaluated at depth minus one, divided by 2 to the power of that depth, tending to 0. No compatibility between successive words is required. -/
structure HalfTerminalOnlyScaledVanishingSequence where
  depth : ℕ → ℕ
  word : ∀ n : ℕ, HalfWord (depth n)
  depth_pos : ∀ n : ℕ, 1 ≤ depth n
  depth_tendsto : Tendsto depth atTop atTop
  zero : ∀ n : ℕ,
    word n ⟨0, Nat.zero_lt_succ (depth n)⟩ = false
  one : ∀ (n : ℕ) (h : 1 < depth n + 1), word n ⟨1, h⟩ = false
  carry_scaled_tendsto :
    Tendsto
      (fun n : ℕ ↦
        |(integerHalfCarry (wordSupport (word n)) (depth n - 1) : ℝ)| /
          (2 : ℝ) ^ depth n)
      atTop (nhds 0)
/-- The universal assertion of the parent problem, named as a proposition so that conditional theorems can refer to it: for every infinite set A of natural numbers the base two series with terms 1 divided by 2 to the power a minus 1, summed over a in A, is irrational. Nothing in this development asserts this proposition. -/
noncomputable def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)
end PalomarCorpus.E257.TerminalScaledVanishing
