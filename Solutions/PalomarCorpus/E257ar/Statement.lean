/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257ar

Every non-theorem declaration of `PalomarCorpus/E257ar/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Sum of the integral quotient contributions of a finite Boolean support. Local copy of Erdos249257.localPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- An exact finite Boolean quotient row at endpoint `n`. Local copy of Erdos249257.ExactLocalMersenneHalfRow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExactLocalMersenneHalfRow (n : ℕ) : Prop :=
  ∃ D : Finset ℕ,
    (∀ d ∈ D, 2 ≤ d ∧ d ≤ n) ∧
      localPrefixQuotient D n = 2 ^ (n - 1) - 1
/-- Exact Boolean quotient rows occur at arbitrarily large endpoints. No compatibility is imposed between the witnesses at different endpoints. Local copy of Erdos249257.CofinalExactLocalMersenneHalfRows, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalExactLocalMersenneHalfRows : Prop :=
  ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ ExactLocalMersenneHalfRow n
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
/-- Positive skipped ranks of the rational half-greedy support occur arbitrarily far out. Positivity separates the skipped-core construction from the already-terminal case in which a finite greedy prefix equals one half exactly. Local copy of Erdos249257.CofinalPositiveHalfGreedySkips, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalPositiveHalfGreedySkips : Prop :=
  ∀ N : ℕ, ∃ c : ℕ,
    max N 4 ≤ c ∧
      0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
      greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
        mersenneWeightRat c
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
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
/-- The discrete square-root strip used by the half-carry search. Local copy of Erdos249257.HalfCarryReachability.halfStripBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- The integer carry whose state at time `N` is the packet's `K_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.integerHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The set of positive exponents selected by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The actual greedy half carry returns to the square-root strip beyond every requested index. This is weaker than an all-level strip bound. Local copy of Erdos249257.HalfCarryReachability.GreedyHalfCarryCofinalStripReturn, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GreedyHalfCarryCofinalStripReturn : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) M ≤
      (halfStripBound (M + 1) : ℤ)
/-- A Boolean support word through exponent `N`. Index zero is retained so restriction is literal; admissibility forces exponents zero and one off. Local copy of Erdos249257.HalfCarryReachability.HalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool
/-- The set represented by a finite Boolean word. Local copy of Erdos249257.HalfCarryReachability.wordSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}
/-- A normalized finite word whose *terminal* integer half-carry is in the discrete square-root strip. There is deliberately no all-prefix admissibility hypothesis here. Local copy of Erdos249257.HalfCarryReachability.HalfTerminalOnlyStripWitness, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfTerminalOnlyStripWitness (M : ℕ) : Prop :=
  ∃ a : HalfWord M,
    a ⟨0, Nat.zero_lt_succ M⟩ = false ∧
    (∀ h : 1 < M + 1, a ⟨1, h⟩ = false) ∧
    |(integerHalfCarry (wordSupport a) (M - 1) : ℝ)| ≤
      (halfStripBound M : ℝ)
/-- Terminal-only square-root-strip witnesses exist at cofinally many depths. The `max N 1` guard makes the terminal index `M - 1` line up with the scaled-residual identity at exponent `M`. Local copy of Erdos249257.HalfCarryReachability.HalfCarryCofinalTerminalOnlyStrip, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfCarryCofinalTerminalOnlyStrip : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, max N 1 ≤ M ∧ HalfTerminalOnlyStripWitness M
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
/-- Integer numerator of the frozen coefficient window. The recurrence uses the binary weights `2^(J-i)` without division. Local copy of Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteCoeffWindowNumerator
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * finiteCoeffWindowNumerator A n J +
        supportCoeff A (n + J + 1)
/-- Binary capacity carried by skipped support bits in the next `J` rows. The earliest skip receives the largest binary weight. Local copy of Erdos249257.HalfCylinderFiniteShadow.futureSkipCapacity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def futureSkipCapacity
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * futureSkipCapacity A n J +
        (by
          classical
          exact if n + J + 1 ∈ A then 0 else 1)
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.extend, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def extend {s : ℕ} (b : SeamRowWord s) (beta : Bool) :
    SeamRowWord (s + 1) :=
  fun i => if h : (i : ℕ) < s - 2 then b ⟨i, h⟩ else beta
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.terminal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def terminal {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord (s + 1)) : Bool :=
  b ⟨s - 2, by omega⟩
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
/-- The binary-boundary target before any selected divisor weights are removed. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamSubsetTarget, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The exact integer weight contributed at seam rank `s` by selecting a proper divisor rank `d < s`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.truncatedMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- The weights with indices `d,d+1,…,s-1`, in descending size order. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega
/-- The actual proper-divisor weight word, indexed by `2,…,s-1`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamWeights, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.seamIntegerGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)
/-- Boolean incidence word aligned with `seamWeightsFrom`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.stemBitsFrom, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def stemBitsFrom (s : ℕ) (P : Finset ℕ) : ℕ → List Bool
  | d =>
      if h : d < s then
        decide (d ∈ P) :: stemBitsFrom s P (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.stemBits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def stemBits (s : ℕ) (P : Finset ℕ) : List Bool :=
  stemBitsFrom s P 2
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- Positive exponents selected through a finite exact-rational greedy run. Local copy of Erdos249257.greedyMersennePrefixRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)
/-- Local copy of Erdos249257.halfGreedyPrefixSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n
/-- The genuinely residual part of the predecessor supply: only a skipped rank immediately before an actual take is exposed. Consecutive skipped ranks have a uniform finite-lookahead proof below. Local copy of Erdos249257.HalfGreedyPreTakePrecriticalSuffixSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedyPreTakePrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    6 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    mersenneWeightRat (c + 1) ≤
      greedyMersenneRemainderRat (1 / 2 : ℚ) c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)
/-- The minimal actual-orbit form of the socket: the quotient lower bound is required only when rank `c` is genuinely skipped by the rational half-greedy orbit. Local copy of Erdos249257.HalfGreedySkippedCriticalQuotientSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedCriticalQuotientSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient
        (insert c (halfGreedyPrefixSupport (c - 1))) (2 * c - 2)
/-- Signed frozen-prefix margin. Its nonnegativity says that the first `J` future divisor-incidence rows cover the centered carry at depth `k`. Local copy of Erdos249257.greedyHalfFrozenMargin, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyHalfFrozenMargin (k J : ℕ) : ℤ :=
  (finiteCoeffWindowNumerator
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℤ) -
    (2 : ℤ) ^ J *
      mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k
/-- Direct full-shell sign socket. It asks only that the actual frozen margin has already crossed by the full-shell horizon at every genuine skipped rank; no seam or abstract adjacent-cut coordinate remains in the hypothesis. Local copy of Erdos249257.HalfGreedySkippedFullShellNonnegative, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedFullShellNonnegative : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    0 ≤ greedyHalfFrozenMargin (n - 1) n
/-- A one-row-earlier form of the actual skipped-rank socket. At endpoint `2c-3` the relevant binary suffix has half the critical capacity. Local copy of Erdos249257.HalfGreedySkippedPrecriticalSuffixSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedPrecriticalSuffixSupply : Prop :=
  ∀ c : ℕ,
    4 ≤ c →
    greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) <
      mersenneWeightRat c →
    localBinarySuffix (halfGreedyPrefixSupport (c - 1)) 1 (2 * c - 3) <
      2 ^ (c - 3)
/-- Exact word-level replacement for the skipped full-shell sign invariant: if a skipped actual word equals the seam-greedy word, its seam remainder must vanish. Local copy of Erdos249257.HalfGreedySkippedSeamAlignmentZero, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedSeamAlignmentZero : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    stemBits n (halfGreedyPrefixSupport (n - 1)) =
        integerGreedyBits (seamWeights n) (seamSubsetTarget n) →
      seamIntegerGreedyRemainder n = 0
/-- Smallest skip-conditioned seam escape socket needed by the actual half orbit. Exceptional seam rows that are actual takes are deliberately absent. Local copy of Erdos249257.HalfGreedySkippedSeamEscape, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HalfGreedySkippedSeamEscape : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    halfStripBound (2 * n) < seamIntegerGreedyRemainder n
/-- A cofinal sequence consists entirely of false successor terminal bits. Local copy of Erdos249257.SeamGreedyCofinalTerminalFalse, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SeamGreedyCofinalTerminalFalse : Prop :=
  ∃ p : ℕ → ℕ, ∃ hp5 : ∀ j, 5 ≤ p j,
    Tendsto p atTop atTop ∧
      ∀ j, terminal
          (by have := hp5 j; omega)
          (seamGreedyWord (p j + 1)) = false
/-- The concrete right-tail predicate, expressed without duplicating the three scalar branch inequalities. Local copy of Erdos249257.SeamGreedyEventuallyRight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SeamGreedyEventuallyRight : Prop :=
  ∃ S : ℕ, 5 ≤ S ∧
    ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true
/-- Along cofinal rows, choose one skipped seam coordinate per row whose rank itself tends to infinity. Local copy of Erdos249257.SeamGreedyUnboundedSkippedRanksAlong, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SeamGreedyUnboundedSkippedRanksAlong (rows : ℕ → ℕ) : Prop :=
  ∃ skip : ∀ j, Fin (rows j - 2),
    Tendsto rows atTop atTop ∧
      Tendsto (fun j => ((skip j : ℕ) + 2)) atTop atTop ∧
        ∀ j, seamGreedyWord (rows j) (skip j) = false
/-- False successor terminal bits occur beyond every requested seam row. Local copy of Erdos249257.SeamGreedyUnboundedTerminalFalse, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SeamGreedyUnboundedTerminalFalse : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, ∃ hp5 : 5 ≤ p,
    N ≤ p ∧
      terminal (by omega)
        (seamGreedyWord (p + 1)) = false
/-- The exact finite Mersenne value of a Boolean lower support. Local copy of Erdos249257.localMersennePrefixValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d
/-- The remaining arithmetic socket in the protected-core construction. Whenever a below-half core is crossed by rank `c`, adjoining `c` must already reach the integral half target at endpoint `2c-2`. By `localBinarySuffix_two_mul_sub_two_lt_criticalCapacity_iff`, this is exactly the sharp `c-2`-bit capacity needed by the strict-upper skipped-core fill. The deficit hypothesis records that `c` is a genuine crossing rank. Local copy of Erdos249257.SkippedCoreCriticalQuotientSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SkippedCoreCriticalQuotientSupply : Prop :=
  ∀ (D : Finset ℕ) (c : ℕ),
    4 ≤ c →
    (∀ d ∈ D, 2 ≤ d ∧ d < c) →
    localMersennePrefixValue D < (1 / 2 : ℚ) →
    (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient (insert c D) (2 * c - 2)
/-- The Erdős–Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
/-- The positive exponents omitted by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSkippedSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- The source-current fractional part of `2^M / (2^d - 1)` for `d ≥ 2`. The exponent is reduced modulo `d` before the division. Local copy of Erdos249257.localMersenneFraction, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneFraction (M d : ℕ) : ℚ :=
  ((2 ^ (M % d) : ℕ) : ℚ) / ((2 ^ d - 1 : ℕ) : ℚ)
/-- Sum of the corresponding fractional contributions. Local copy of Erdos249257.localFractionMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localFractionMass (D : Finset ℕ) (M : ℕ) : ℚ :=
  ∑ d ∈ D, localMersenneFraction M d
/-- The quotient of one scaled Mersenne weight written without division: a shift by the Euclidean remainder times a finite geometric word. Local copy of Erdos249257.localMersenneGeometricQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneGeometricQuotient (M d : ℕ) : ℕ :=
  2 ^ (M % d) * ∑ j ∈ Finset.range (M / d), (2 ^ d) ^ j
/-- The corresponding geometric normal form of a finite prefix quotient. Local copy of Erdos249257.localGeometricPrefixQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localGeometricPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneGeometricQuotient M d
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- The natural exponent support encoded by a finite seam word. Local copy of Erdos249257.seamWordSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
/-- Delta for a selected prefix. This applies in particular to the integer greedy take set; the identity itself needs no greediness hypothesis. Local copy of ErdosProblems.Erdos257.PaperCompleteR20.rowDeviation, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowDeviation (n : ℕ) (D : Finset ℕ) : ℤ :=
  (2 : ℤ)^(2*n-1) - (2 : ℤ)^(n+1) - ∑ d ∈ D, (truncatedMersenneWeight n d : ℤ)
end PalomarCorpus.E257.PaperStatementsAR
