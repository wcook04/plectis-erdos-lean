/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band d

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

namespace PalomarCorpus.E257.PaperStatementsD
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
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
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
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
/-- The set of positive exponents selected by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The actual greedy half carry returns to the square-root strip beyond every requested index. This is weaker than an all-level strip bound. Local copy of Erdos249257.HalfCarryReachability.GreedyHalfCarryCofinalStripReturn, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GreedyHalfCarryCofinalStripReturn : Prop :=
  ∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧
    integerHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) M ≤
      (halfStripBound (M + 1) : ℤ)
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The Erdős–Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The finite Erdős partial sum `∑_{n ∈ F} 1 / (b ^ n - 1)` as a rational number, stated with subtraction in `ℚ` so the statement reads exactly like the mathematical series. Local copy of Erdos249257.finiteErdosSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)
/-- Positive exponents selected through a finite exact-rational greedy run. Local copy of Erdos249257.greedyMersennePrefixRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)
/-- The positive exponents omitted by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSkippedSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- The first geometric channel of the Mersenne tail. Local copy of Erdos249257.halfDyadicCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfDyadicCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
/-- For a displayed residual `p / (2L)`, the integer numerator of its excess above the next dyadic point `2^-(n+1)`. Indeed, `p/(2L) - 2^-(n+1) = E/(2^(n+1)L)`. Keeping `E` integral makes the unresolved skipped-branch comparison an exact Diophantine inequality rather than a real-valued phase estimate. Local copy of Erdos249257.nextDyadicExcessIntNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)
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
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- Literal finite internal gap over a positive finite prefix. Local copy of ErdosProblems.Erdos257.PaperCompleteR20.InternalMersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def InternalMersenneGap (x : ℝ) : Prop :=
  ∃ (D : Finset ℕ) (m : ℕ), 1 ≤ m ∧
    (∀ n ∈ D, 0 < n ∧ n < m) ∧
    positiveMersenneSupportValue (D : Set ℕ)+mersenneTail m < x ∧
    x < positiveMersenneSupportValue (D : Set ℕ)+mersenneWeight m
/-- States record:257rig-c18 from the long record for Erdős problem #257. Transported from Erdos249257.HalfCarryReachability.greedy_half_infinite_of_cofinalStripReturn in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_half_infinite_of_cofinalStripReturn
    (hreturn : GreedyHalfCarryCofinalStripReturn) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  sorry
/-- States thm:sqrt-bound-route from the long record for Erdős problem #257. Transported from Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_sqrtBound
    (hnonneg : ∀ N : ℕ,
      0 ≤ mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N)
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  sorry
/-- States record:257rig-c16 from the long record for Erdős problem #257. Transported from Erdos249257.HalfCarryReachability.greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_half_infinite_of_mobiusCenteredHalfCarry_upperBound
    (hbound : ∀ N : ℕ,
      (mobiusCenteredHalfCarry
        (greedyMersenneSupport (1 / 2 : ℝ)) N : ℝ) ≤
          2 * Real.sqrt (N : ℝ) + 4) :
    (greedyMersenneSupport (1 / 2 : ℝ)).Infinite ∧
      erdosSupportSeries 2 (greedyMersenneSupport (1 / 2 : ℝ)) =
        (1 : ℝ) / 2 := by
  sorry
/-- States record:257rig-c16, thm:sqrt-bound-route from the long record for Erdős problem #257. Transported from Erdos249257.HalfCarryReachability.greedy_mobiusCenteredHalfCarry_nonneg in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_mobiusCenteredHalfCarry_nonneg (N : ℕ) :
    0 ≤ mobiusCenteredHalfCarry (greedyMersenneSupport (1 / 2 : ℝ)) N := by
  sorry
/-- States record:257bm-c2 from the long record for Erdős problem #257. Transported from Erdos249257.cofinalPositiveHalfGreedySkips_iff_half_mem in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cofinalPositiveHalfGreedySkips_iff_half_mem :
    CofinalPositiveHalfGreedySkips ↔
      (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States lem:dyadic-excess-reformulation from the long record for Erdős problem #257. Transported from Erdos249257.greedyHalf_mem_nextMersenneDyadicSliver_iff_excess in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedyHalf_mem_nextMersenneDyadicSliver_iff_excess (n : ℕ) :
    (halfDyadicCap (n + 1) <
          greedyMersenneRemainder (1 / 2 : ℝ) n ∧
        greedyMersenneRemainder (1 / 2 : ℝ) n <
          mersenneWeight (n + 1)) ↔
      (0 < halfGreedyNextDyadicExcessNumerator n ∧
        2 * halfGreedyNextDyadicExcessNumerator n <
          halfGreedyResidualDisplayedNumerator n) := by
  sorry
/-- States thm:last-skip-iff-fatal from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_iff_every_actual_skip_survives in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_iff_every_actual_skip_survives :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M := by
  sorry
/-- States record:257bm-c2 from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States prop:collapse from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.greedy_half_of_cofinal_upper_carry in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_half_of_cofinal_upper_carry (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1 : ℝ)/2 := by
  sorry
/-- States thm:greedy-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.paper_greedy_survival in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedy_survival :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x)) := by
  sorry
end PalomarCorpus.E257.PaperStatementsD
