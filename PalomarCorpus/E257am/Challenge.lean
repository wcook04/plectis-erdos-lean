/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band m

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

namespace PalomarCorpus.E257.PaperStatementsAM
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
/-- A real number represented by an integer numerator and a positive natural denominator. This is the explicit positive-denominator form of membership in `ℚ`; it keeps the carry multiplier visible in theorem statements. Local copy of Erdos249257.HasRationalValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
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
/-- Local copy of Erdos249257.halfGreedyPrefixSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n
/-- Signed frozen-prefix margin. Its nonnegativity says that the first `J` future divisor-incidence rows cover the centered carry at depth `k`. Local copy of Erdos249257.greedyHalfFrozenMargin, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyHalfFrozenMargin (k J : ℕ) : ℤ :=
  (finiteCoeffWindowNumerator
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℤ) -
    (2 : ℤ) ^ J *
      mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k
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
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- One term of the binary coding of the achievement set. Local copy of Erdos249257.mersenneDigitTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)
/-- The positive gap between one Mersenne weight and the tail after it. Local copy of Erdos249257.mersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n
/-- The support value coded by a binary sequence. Local copy of Erdos249257.positiveMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b
/-- Literal finite internal gap over a positive finite prefix. Local copy of ErdosProblems.Erdos257.PaperCompleteR20.InternalMersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def InternalMersenneGap (x : ℝ) : Prop :=
  ∃ (D : Finset ℕ) (m : ℕ), 1 ≤ m ∧
    (∀ n ∈ D, 0 < n ∧ n < m) ∧
    positiveMersenneSupportValue (D : Set ℕ)+mersenneTail m < x ∧
    x < positiveMersenneSupportValue (D : Set ℕ)+mersenneWeight m
/-- The common denominator `∏_{k=1}^{N} (2^k - 1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.mersenneDen, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneDen (N : ℕ) : ℕ := ∏ k ∈ Finset.range N, (2 ^ (k + 1) - 1)
/-- `2 * mersenneDen N * mersenneWeight n`, an exact natural number whenever `1 ≤ n ≤ N`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.scaledMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scaledMersenneWeight (N n : ℕ) : ℕ := (2 * mersenneDen N) / (2 ^ n - 1)
/-- The scaled rational upper bound for the tail `mersenneTail (d+1)`: the exact weights of ranks `d+2, …, N` plus the enclosure `mersenneTail N < mersenneWeight N`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.certifiedTailBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedTailBound (d N : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (N - (d + 1)), scaledMersenneWeight N (d + 1 + 1 + j))
    + scaledMersenneWeight N N
/-- The scaled value of the finite word coded by a list of bits: bit `i` of the list selects the Mersenne exponent `i + 1`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.certifiedWordValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedWordValue (L : List Bool) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range L.length,
    bif L.getD i false then scaledMersenneWeight N (i + 1) else 0
/-- The finite certificate: a bit word of length `d`, a cutoff `N ≥ d + 1`, and two exact natural-number inequalities saying that the coded word already overshoots `1/2` after the skip at rank `d + 1`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.FatalHalfGapCertificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FatalHalfGapCertificate (p : List Bool × ℕ) : Prop :=
  p.1.length + 1 ≤ p.2 ∧
    certifiedWordValue p.1 p.2 + certifiedTailBound p.1.length p.2 < mersenneDen p.2 ∧
      mersenneDen p.2 <
        certifiedWordValue p.1 p.2 + scaledMersenneWeight p.2 (p.1.length + 1)
/-- The finite Mersenne word coded by a list of bits. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.certWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certWord (L : List Bool) : Finset ℕ :=
  ((Finset.range L.length).filter fun i => L.getD i false = true).image (· + 1)
/-- The greedy rule applied to an arbitrary target `t` and an arbitrary weight system `v`, in increasing order of rank, starting at rank `2`. `tailGreedyRemainder t v m` is the residual after the ranks `2, …, m + 1`, so the decision at rank `n ≥ 2` is `v n ≤ tailGreedyRemainder t v (n - 2)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailGreedyRemainder (t : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | m + 1 =>
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m
/-- Binary digit strings supported on `J`. Local copy of ErdosProblems.Erdos257.SupportedMersenneDigits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}
/-- The ordinary Mersenne digit map restricted to a chosen support. Local copy of ErdosProblems.Erdos257.supportedMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1
/-- The achievement set obtained by allowing digits only on `J`. Local copy of ErdosProblems.Erdos257.supportedMersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)
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
/-- States thm:master-dichotomy from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ¬ ExistsFatalHalfGap := by
  sorry
/-- States record:257bm-c2 from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_positiveHalfGreedySkips
    (hskips : CofinalPositiveHalfGreedySkips) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry
/-- States thm:master-dichotomy from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_or_exists_fatal_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_or_exists_fatal_gap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
          < 1 / 2 ∧
        (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
          + mersenneWeight (d + 1) := by
  sorry
/-- States lem:half-endpoint-kills from the long record for Erdős problem #257. Transported from Erdos249257.half_ne_coe_finset_add_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_ne_coe_finset_add_mersenneTail
    (u : Finset ℕ) (d : ℕ) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
      ≠ (1 / 2 : ℝ) := by
  sorry
/-- States record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.mersenneGap_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneGap_le {n : ℕ} (hn : 0 < n) :
    mersenneGap n ≤ (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n + 3 * ((1 : ℝ) / 8) ^ n := by
  sorry
/-- States lem:gap-mass-summability, record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.mersenneGap_tail_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneGap_tail_le (N : ℕ) :
    ∑' k : ℕ, mersenneGap (N + k + 1)
      ≤ (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N := by
  sorry
/-- States lem:half-endpoint-kills from the long record for Erdős problem #257. Transported from Erdos249257.positiveMersenneSupportValue_coe_finset_ne_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem positiveMersenneSupportValue_coe_finset_ne_half
    {u : Finset ℕ} (h0 : 0 ∉ u) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≠ (1 / 2 : ℝ) := by
  sorry
/-- States record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.summable_mersenneGap_shift in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem summable_mersenneGap_shift (N : ℕ) :
    Summable (fun k : ℕ => mersenneGap (N + k + 1)) := by
  sorry
/-- States lem:gap-mass-summability from the long record for Erdős problem #257. Transported from Erdos249257.summable_mersenneGap_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem summable_mersenneGap_succ : Summable (fun k : ℕ => mersenneGap (k + 1)) := by
  sorry
/-- States lem:gap-mass-summability, record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.tendsto_mersenneGap_tail_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tendsto_mersenneGap_tail_zero :
    Tendsto (fun N : ℕ => ∑' k : ℕ, mersenneGap (N + k + 1)) atTop (nhds 0) := by
  sorry
/-- States prop:collapse from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.greedy_half_of_cofinal_upper_carry in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_half_of_cofinal_upper_carry (C D : ℝ)
    (h : ∀ K : ℕ, ∃ N : ℕ, K ≤ N ∧
      (integerHalfCarry (greedyMersenneSupport (1/2 : ℝ)) N : ℝ) ≤
        C*Real.sqrt ((N : ℝ)+1)+D) :
    erdosSupportSeries 2 (greedyMersenneSupport (1/2 : ℝ)) = (1 : ℝ)/2 := by
  sorry
/-- States thm:real-form from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.mersenne_constant_decimal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenne_constant_decimal :
    (1066951524152917 : ℝ)/10^16 < erdosBorweinMersenneConstant-3/2 ∧
      erdosBorweinMersenneConstant-3/2 < (1066951524152918 : ℝ)/10^16 := by
  sorry
/-- States thm:topology from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.mersenne_topology_quantitative in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenne_topology_quantitative : := by
  sorry
/-- States thm:geometry, thm:topology from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.paper_achievement_geometry in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_achievement_geometry :
    IsCompact mersenneAchievementSet ∧ IsClosed mersenneAchievementSet ∧
    Perfect mersenneAchievementSet ∧ IsTotallyDisconnected mersenneAchievementSet ∧
    IsNowhereDense mersenneAchievementSet ∧ volume mersenneAchievementSet = 1 ∧
    convexHull ℝ mersenneAchievementSet = Icc 0 erdosBorweinMersenneConstant ∧
    Function.Injective positiveMersenneDigitValue ∧
    ∀ x ∈ mersenneAchievementSet, ∃! A : Set ℕ,
      0 ∉ A ∧ positiveMersenneSupportValue A = x := by
  sorry
/-- States thm:greedy-survival from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.paper_greedy_survival in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedy_survival :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
    (∀ x : ℝ, 0 ≤ x → x ≤ erdosBorweinMersenneConstant →
      (x ∉ mersenneAchievementSet ↔ InternalMersenneGap x)) := by
  sorry
/-- States thm:real-form from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.row_constant_eq_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem row_constant_eq_tail :
    erdosBorweinMersenneConstant-3/2 = mersenneTail 1-1/2 := by
  sorry
/-- States thm:seam-limit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.abs_supportValue_sub_le_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_supportValue_sub_le_mersenneTail {A B : Set ℕ} {K : ℕ}
    (h : ∀ d : ℕ, 1 ≤ d → d ≤ K → (d ∈ A ↔ d ∈ B)) : := by
  sorry
/-- States prop:one-orbit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.approx_orbit_induction in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem approx_orbit_induction
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n))) :
    ∀ r : ℕ,
      Filter.Tendsto (fun j => tailGreedyRemainder (t j) (v j) r) Filter.atTop
          (nhds (greedyMersenneRemainder (1 / 2 : ℝ) (r + 1))) ∧
        ∀ᶠ j in Filter.atTop, ∀ n : ℕ, 2 ≤ n → n ≤ r + 1 →
          ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
            (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))) := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.certificate_of_existsFatalHalfGap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certificate_of_existsFatalHalfGap (h : ExistsFatalHalfGap) :
    ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.certifiedTailBound_cast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedTailBound_cast {d N : ℕ} (hdN : d + 1 ≤ N) :
    (certifiedTailBound d N : ℝ)
      = 2 * (mersenneDen N : ℝ) *
          ((∑ j ∈ Finset.range (N - (d + 1)), mersenneWeight (d + 1 + 1 + j))
            + mersenneWeight N) := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.certifiedWordValue_cast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedWordValue_cast {L : List Bool} {N : ℕ} (hLN : L.length ≤ N) :
    (certifiedWordValue L N : ℝ)
      = 2 * (mersenneDen N : ℝ) * ∑ n ∈ certWord L, mersenneWeight n := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.depth_prefix_interval_disjoint in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem depth_prefix_interval_disjoint {t : ℝ} {u v : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d) (hv : ∀ n ∈ v, 0 < n ∧ n ≤ d)
    (hut : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d)
    (hvt : positiveMersenneSupportValue (↑v : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑v : Set ℕ) + mersenneTail d) :
    u = v := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_iff_exists_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem existsFatalHalfGap_iff_exists_certificate :
    ExistsFatalHalfGap ↔ ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_of_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem existsFatalHalfGap_of_certificate {L : List Bool} {N : ℕ}
    (h : FatalHalfGapCertificate (L, N)) : ExistsFatalHalfGap := by
  sorry
/-- States thm:fatal-absorbing from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_absorbing in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_absorbing {x : ℝ} (hx : 0 ≤ x) :
    (∀ n : ℕ, mersenneTail n < greedyMersenneRemainder x n →
        (∀ k : ℕ, n + k + 1 ∈ greedyMersenneSupport x) ∧
          ∀ k : ℕ, mersenneTail (n + k) < greedyMersenneRemainder x (n + k)) ∧
      ((greedyMersenneSkippedSupport x).Infinite → x ∈ mersenneAchievementSet) := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_endpoint_bounds in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_gap_endpoint_bounds {A : Set ℕ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hagree : ∀ n : ℕ, 0 < n → n ≤ d → (n ∈ A ↔ n ∈ u)) :
    (d + 1 ∉ A →
        positiveMersenneSupportValue A
          ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)) ∧
      (d + 1 ∈ A →
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)
          ≤ positiveMersenneSupportValue A) := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_excludes_every_representation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_gap_excludes_every_representation {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    ∀ A : Set ℕ, 0 ∉ A → positiveMersenneSupportValue A ≠ t := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_within_prefix_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_gap_within_prefix_interval {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d := by
  sorry
/-- States lem:no-ties from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.irrational_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_mersenneTail : ∀ n : ℕ, Irrational (mersenneTail n) := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.mersenneTail_eq_sum_add in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneTail_eq_sum_add (m K : ℕ) :
    mersenneTail m
      = (∑ j ∈ Finset.range K, mersenneWeight (m + 1 + j)) + mersenneTail (m + K) := by
  sorry
/-- States prop:achievement-set-topology from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_achievement_set_topology in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_achievement_set_topology :
    Continuous positiveMersenneDigitValue ∧
      Set.range positiveMersenneDigitValue = mersenneAchievementSet ∧
      IsCompact mersenneAchievementSet ∧
      IsClosed mersenneAchievementSet ∧
      Perfect mersenneAchievementSet ∧
      IsTotallyDisconnected mersenneAchievementSet ∧
      IsNowhereDense mersenneAchievementSet ∧
      volume mersenneAchievementSet = 1 := by
  sorry
/-- States prop:cpgs-equiv from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_cpgs_equiv in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_cpgs_equiv :
    ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
        0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
        greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
      ↔ CofinalPositiveHalfGreedySkips) ∧
      (∀ n : ℕ, 0 < greedyMersenneRemainderRat (1 / 2 : ℚ) n) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ ∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
            greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite) ∧
      ((∀ N : ℕ, ∃ c : ℕ, N ≤ c ∧
          0 < greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) ∧
          greedyMersenneRemainderRat (1 / 2 : ℚ) (c - 1) < mersenneWeightRat c)
        ↔ (1 / 2 : ℝ) ∈ mersenneAchievementSet) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_effective_horizon_test in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_effective_horizon_test (k J : ℕ)
    (heta : 0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)
    (htest : ((k + J + 3 : ℕ) : ℝ) / (2 : ℝ) ^ J <
      1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) :
    0 < greedyHalfFrozenMargin k J := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_eq_coeffTail_sub_carry in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_eta_eq_coeffTail_sub_carry (k : ℕ) :
    1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k =
      binaryCoeffTail
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ)) (k + 1) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_eta_hasRationalValue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_eta_hasRationalValue (k : ℕ) :
    HasRationalValue
      (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_eventual_nonnegative_margin_equivalence in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_eventual_nonnegative_margin_equivalence {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) ↔
      ∃ J : ℕ, 0 ≤ greedyHalfFrozenMargin k J := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_mass_threshold in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exact_mass_threshold {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ mersenneTail k ↔
        (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ≤ (a : ℝ) / u) ∧
      0 < (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ∧
      (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) < 2 / 3 := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_limit_pos_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_limit_pos_iff (k : ℕ) :
    0 < 1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k ↔
      greedyMersenneRemainder (1 / 2 : ℝ) k < halfDyadicCap (k + 1) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_monotone in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_normalised_monotone (k : ℕ) :
    Monotone (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_tendsto in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_normalised_tendsto (k : ℕ) :
    Tendsto (fun J : ℕ ↦ (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J)
      atTop
      (nhds (1 - (2 : ℝ) ^ (k + 1) * greedyMersenneRemainder (1 / 2 : ℝ) k)) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_frozen_margin_normalised_value in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_frozen_margin_normalised_value (k J : ℕ) :
    (greedyHalfFrozenMargin k J : ℝ) / (2 : ℝ) ^ J =
      (∑ i ∈ Finset.Icc 1 J,
          (supportCoeff (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1 + i) : ℝ) /
            (2 : ℝ) ^ i) -
        (mobiusCenteredHalfCarry (↑(halfGreedyPrefixSupport k) : Set ℕ) k : ℝ) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_greedyHalfRemainder_ne_dyadicCap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_greedyHalfRemainder_ne_dyadicCap {k : ℕ} (hk : 0 < k) :
    greedyMersenneRemainder (1 / 2 : ℝ) k ≠ halfDyadicCap (k + 1) := by
  sorry
/-- States record:257bm-c19 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_halfGreedyPrefixSupport_eq_greedy_inter_Icc (k : ℕ) :
    (↑(halfGreedyPrefixSupport k) : Set ℕ) =
      greedyMersenneSupport (1 / 2 : ℝ) ∩ Set.Icc 2 k := by
  sorry
/-- States lem:no-ties from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_no_ties (k : ℕ) (hk : 2 ≤ k) :
    greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneWeight k ∧
      greedyMersenneRemainder (1 / 2 : ℝ) (k - 1) ≠ mersenneTail k := by
  sorry
/-- States lem:no-ties from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_skip in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_no_ties_skip (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneTail (n + 1) := by
  sorry
/-- States lem:no-ties from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_no_ties_take in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_no_ties_take (n : ℕ) :
    greedyMersenneRemainder (1 / 2 : ℝ) n ≠ mersenneWeight (n + 1) := by
  sorry
/-- States prop:one-orbit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_one_orbit_stability in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_one_orbit_stability
    (t : ℕ → ℝ) (v : ℕ → ℕ → ℝ) (dep : ℕ → ℕ)
    (ht : Filter.Tendsto t Filter.atTop (nhds (1 / 2 : ℝ)))
    (hv : ∀ n : ℕ, 2 ≤ n →
      Filter.Tendsto (fun j => v j n) Filter.atTop (nhds (mersenneWeight n)))
    (hvpos : ∀ j n : ℕ, 0 < v j n)
    (hdep : Filter.Tendsto dep Filter.atTop Filter.atTop)
    (K : ℕ) :
    ∀ᶠ j in Filter.atTop, K ≤ dep j ∧
      ∀ n : ℕ, 2 ≤ n → n ≤ K →
        ((v j n ≤ tailGreedyRemainder (t j) (v j) (n - 2)) ↔
          (mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sided_finite_decision_boundary in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_one_sided_finite_decision_boundary :
    (∀ x : ℝ, x ∈ mersenneAchievementSet ↔
        0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) ∧
      (∀ x : ℝ, (∃ n : ℕ, mersenneTail n < greedyMersenneRemainder x n) →
        x ∉ mersenneAchievementSet) ∧
      (∀ x : ℝ, x ∈ mersenneAchievementSet →
        ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) := by
  sorry
/-- States thm:sharp-fatal-gap from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_fatal_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_fatal_gap :
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ (u : ℝ) / (2 * L) < mersenneWeight k)) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ ¬ (mersenneWeight k ≤ (u : ℝ) / (2 * L)))) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k ↔ u ≤ a)) ∧
    (∀ k : ℕ, (1 : ℝ) / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        2 * u ≤ 3 * a → (u : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ u a : ℕ, u ≤ a → 2 * u ≤ 3 * a) ∧
    ((2 : ℕ) ^ 2 * 7 + 5 = 2 * 13 + 7 ∧ 2 * 7 ≤ 3 * 5 ∧ ¬ (7 ≤ 5) ∧
      (1 : ℝ) / 2 ^ 2 < (7 : ℝ) / (2 * 13) ∧ (7 : ℝ) / (2 * 13) < mersenneTail 2) ∧
    (∀ k L : ℕ, 1 ≤ k → 2 ^ k * 3 + 2 ≠ 2 * L + 3) ∧
    (∀ k L a : ℕ, 1 ≤ k → 0 < a → 2 ^ k * 1 + a = 2 * L + 1 →
        (1 : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        mersenneTail k < (u : ℝ) / (2 * L) →
        3 * a < 2 * u ∧ 2 ≤ u ∧ (Odd u → 3 ≤ u)) := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_actual_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_skip_safe_actual_tail {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTail k := by
  sorry
/-- States prop:strip-equiv from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_terminal_strip_equiv in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_terminal_strip_equiv :
    ((∀ N : ℕ, ∃ M : ℕ, N ≤ M ∧ ∃ D : Finset ℕ,
        (∀ d ∈ D, 2 ≤ d ∧ d ≤ M) ∧ := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_volume_supportedMersenneAchievementSet_dichotomy in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ENNReal) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0) := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.scaledMersenneWeight_cast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaledMersenneWeight_cast {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (scaledMersenneWeight N n : ℝ) = 2 * (mersenneDen N : ℝ) * mersenneWeight n := by
  sorry
/-- States thm:straddle-closed-set from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.straddle_all_depths_iff_mem in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem straddle_all_depths_iff_mem (t : ℝ) :
    (∀ d : ℕ, ∃ D : Finset ℕ, (∀ n ∈ D, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑D : Set ℕ) ≤ t ∧
        t ≤ positiveMersenneSupportValue (↑D : Set ℕ) + mersenneTail d) ↔
      t ∈ mersenneAchievementSet := by
  sorry
/-- States thm:straddle-closed-set from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.straddle_limiting_support_inputs in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem straddle_limiting_support_inputs :
    IsCompact mersenneAchievementSet ∧
      Filter.Tendsto mersenneTail Filter.atTop (nhds 0) := by
  sorry
/-- States prop:one-orbit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.tailGreedyRemainder_mersenne in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailGreedyRemainder_mersenne (m : ℕ) :
    tailGreedyRemainder (1 / 2 : ℝ) mersenneWeight m
      = greedyMersenneRemainder (1 / 2 : ℝ) (m + 1) := by
  sorry
/-- States thm:supported-dichotomy from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem perfect_supportedMersenneAchievementSet
    {J : Set ℕ} (hJ : J.Infinite) :
    Perfect (supportedMersenneAchievementSet J) := by
  sorry
/-- States thm:supported-dichotomy from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.supportedMersenneDigitValue_injective in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supportedMersenneDigitValue_injective (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) := by
  sorry
/-- States thm:supported-dichotomy from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧
        volume (supportedMersenneAchievementSet J) = 0) := by
  sorry
/-- States thm:supported-dichotomy from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite
    {J : Set ℕ} (hJ : Jᶜ.Infinite) :
    volume (supportedMersenneAchievementSet J) = 0 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAM
