/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #251, record sections 5 to 8: the tail recurrence and the exact criteria; a local certificate, and one actual pair; two lower bounds on a possible rational denominator

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #251, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #251 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Filter
open Topology
open Finset
open Filter Topology

namespace PalomarCorpus.E251_02.Shared
/-- The same dyadic tail recurrence with integer digits `g` for a real sequence: `T (N + 1) = 2 * T N - g (N + 1)` at every index `N`, with the integer digit cast into the reals. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A real number is integral when it equals the cast of an integer. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- The zero-based enumeration of the primes in increasing order, so that `prime0 0 = 2`, `prime0 1 = 3`, and `prime0 n` is the `(n + 1)`st prime. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- The term of the normalised prime dyadic series: the `(n + 1)`st prime, cast to a real number, divided by `2 ^ (n + 1)`. The sum over `n` at least 0 is `2/2 + 3/4 + 5/8` and so on, the value whose irrationality Erdős problem 251 asks about. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)
/-- The `n`th consecutive prime gap in the zero-based indexing, `prime0 (n + 1) - prime0 n`. The subtraction is truncated subtraction of natural numbers, which agrees with the ordinary difference because the primes increase; the first values are 1, 2, 2, 4, 2, 4. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
/-- The term of the consecutive-prime-gap dyadic series: the `n`th prime gap, cast to a real number, divided by `2 ^ (n + 1)`. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)
/-- The exact rational partial sum of the first `n` terms of the prime-gap dyadic series, the finite sum over `i` in `Finset.range n` of `primeGap0 i / 2 ^ (i + 1)` computed in the rationals. -/
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)
/-- The genuine scaled tail after the first `N+1` prime-gap terms. Local copy of ErdosProblems.Erdos251.realPrimeGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))
/-- The shift of length `h` at basepoint `N` of a real orbit, namely the difference `T (N + h) - T N`. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
end PalomarCorpus.E251_02.Shared

namespace PalomarCorpus.E251.PaperStatementsL
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (RealIntegral prime0 primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail)
/-- **(P)**: for every positive modulus and every cutoff, some pair of indices beyond the cutoff, congruent modulo the modulus, has a nonintegral tail difference. Local copy of ErdosProblems.Erdos251.CofinalFreePairNonintegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalFreePairNonintegral (T : ℕ → ℝ) : Prop :=
  ∀ t : ℕ, 0 < t → ∀ N₀ : ℕ, ∃ N M : ℕ, N₀ ≤ N ∧ N₀ ≤ M ∧ N ≡ M [MOD t] ∧
    ¬ RealIntegral (T M - T N)
/-- States long251:res:freepair from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.actual_free_pair_criterion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actual_free_pair_criterion :
    Irrational (∑' n : ℕ, primeGapDyadicTerm n) ↔
      CofinalFreePairNonintegral realPrimeGapTail := by
  sorry
end PalomarCorpus.E251.PaperStatementsL

namespace PalomarCorpus.E251.PaperStatementsM
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (RealDyadicTailRecurrence RealIntegral realTailShift)
/-- The least common multiple of the positive integers seen so far. Local copy of ErdosProblems.Erdos251.lcmDiagonalSchedule, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmDiagonalSchedule : ℕ → ℕ
  | 0 => 1
  | j + 1 => Nat.lcm (lcmDiagonalSchedule j) (j + 1)
/-- States long251:res:lcmdiagonal from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.irrational_initial_iff_all_lcmDiagonal_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_initial_iff_all_lcmDiagonal_nonintegral {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    Irrational (T 0) ↔
      ∀ j : ℕ,
        ¬ RealIntegral
          (realTailShift T (lcmDiagonalSchedule j) (lcmDiagonalSchedule j)) := by
  sorry
end PalomarCorpus.E251.PaperStatementsM

namespace PalomarCorpus.E251.PaperStatementsG
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (RealDyadicTailRecurrence RealIntegral prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail realTailShift)
/-- Abstract dyadic tail recurrence with integer digits. The rational candidate state below is an exact actual-gap instance; identifying a candidate with the genuine infinite sum remains analytic. Local copy of ErdosProblems.Erdos251.DyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A rational number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RatIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
/-- States long251:res:gap-nonperiodic, res:gap-nonperiodic from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.prime_gaps_not_eventually_periodic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime_gaps_not_eventually_periodic {h : ℕ} (hh : 0 < h) :
    ¬ ∃ N₀, ∀ N, N₀ ≤ N → primeGap0 (N + h) = primeGap0 N := by
  sorry
/-- States long251:res:boundedperturbation from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.rational_bounded_perturbation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_bounded_perturbation {a : ℕ → ℕ}
    (ha : Summable (fun n => (a n : ℝ) / 2 ^ (n + 1)))
    (M K : ℕ) (hM : 0 < M) :
    ∃ (δ : ℕ → ℕ) (r : ℚ),
      (∀ n, δ n = 0 ∨ δ n = 1) ∧
      (∀ n < K, δ n = 0) ∧
      HasSum (fun n => ((a n + M * δ n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) := by
  sorry
/-- States long251:res:smallpair from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.rational_small_pair_bundle in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_small_pair_bundle {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (h : ℕ) :
    (∀ N, ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
      (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) →
      g (N + h + 1) ≠ g (N + 1) →
      ¬ (RatIntegral (tailShift T h N) ∧ RatIntegral (tailShift T h (N + 1)))) ∧
    ((∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < tailShift T h N ∧ tailShift T h N < 1) ∧
       (-1 < tailShift T h (N + 1) ∧ tailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N)) := by
  sorry
/-- States long251:res:signedwindow from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.real_signed_two_window in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_signed_two_window {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (heven : ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) :
    (-1 < realTailShift T h N ∧ realTailShift T h N < 1 ∧
      -1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1 ∧
      g (N + h + 1) ≠ g (N + 1)) ↔
    ((g (N + h + 1) - g (N + 1) = 2 ∧
       1 / 2 < realTailShift T h N ∧ realTailShift T h N < 1) ∨
     (g (N + h + 1) - g (N + 1) = -2 ∧
       -1 < realTailShift T h N ∧ realTailShift T h N < -(1 / 2))) := by
  sorry
/-- States long251:res:smallpair-real from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.real_small_pair_prime_endpoint in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_small_pair_prime_endpoint {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h : ℕ) :
    (∀ N, ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
      (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) →
      g (N + h + 1) ≠ g (N + 1) →
      ¬ (RealIntegral (realTailShift T h N) ∧ RealIntegral (realTailShift T h (N + 1)))) ∧
    ((∀ N₀, ∃ N, N₀ ≤ N ∧
      ((-1 < realTailShift T h N ∧ realTailShift T h N < 1) ∧
       (-1 < realTailShift T h (N + 1) ∧ realTailShift T h (N + 1) < 1)) ∧
      g (N + h + 1) ≠ g (N + 1)) →
      ¬ ∃ N₀, ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) ∧
    ((∀ h' : ℕ, 0 < h' → ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ((-1 < realTailShift realPrimeGapTail h' N ∧
        realTailShift realPrimeGapTail h' N < 1) ∧
       (-1 < realTailShift realPrimeGapTail h' (N + 1) ∧
        realTailShift realPrimeGapTail h' (N + 1) < 1)) ∧
      primeGap0 (N + h' + 1) ≠ primeGap0 (N + 1)) →
      Irrational (∑' n : ℕ, primeDyadicTerm n)) := by
  sorry
end PalomarCorpus.E251.PaperStatementsG

namespace PalomarCorpus.E251.PaperStatementsO
open Filter
open Topology
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (RealIntegral prime0 primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail realTailShift)
/-- Real quartic from the displayed remainder, with all constants unchanged. Local copy of ErdosProblems.Erdos251.PaperR7.quarticTailPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quarticTailPolynomial (x : ℝ) : ℝ :=
  x ^ 4 + 8 * x ^ 3 + 36 * x ^ 2 + 104 * x + 150
/-- Local copy of ErdosProblems.Erdos251.PaperR7.explicitRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def explicitRemainder (h N L : ℕ) : ℝ :=
  1250 / 2 ^ L * (quarticTailPolynomial ((N : ℝ) + h + L + 2) +
    quarticTailPolynomial ((N : ℝ) + L + 2))
/-- Euclidean distance to the complete integer lattice. Local copy of ErdosProblems.Erdos251.PaperR7.integerDistance, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerDistance (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ)))
/-- Local copy of ErdosProblems.Erdos251.PaperR7.signedWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def signedWindow (h N L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L,
    ((primeGap0 (N + h + j + 1) : ℝ) - primeGap0 (N + j + 1)) / 2 ^ (j + 1)
/-- States long251:res:explicit-remainder from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.explicit_remainder_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem explicit_remainder_certificate (h N L : ℕ) :
    |realTailShift realPrimeGapTail h N - signedWindow h N L| ≤ explicitRemainder h N L ∧
    (|signedWindow h N L| + explicitRemainder h N L < 1 →
      |realTailShift realPrimeGapTail h N| < 1) ∧
    (explicitRemainder h N L < integerDistance (signedWindow h N L) →
      ¬ RealIntegral (realTailShift realPrimeGapTail h N)) := by
  sorry
end PalomarCorpus.E251.PaperStatementsO

namespace PalomarCorpus.E251.PaperStatementsP
open scoped BigOperators
open Finset
export PalomarCorpus.E251_02.Shared (RealIntegral prime0 primeGap0 primeGapDyadicTerm primeGapPartialSumQ realPrimeGapTail realTailShift)
/-- States long251:res:finite-smallpair from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.finite_small_pair in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_small_pair :
    (-1 < realTailShift realPrimeGapTail 1 2 ∧
      realTailShift realPrimeGapTail 1 2 < 1) ∧
    (-1 < realTailShift realPrimeGapTail 1 3 ∧
      realTailShift realPrimeGapTail 1 3 < 1) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 2) ∧
    ¬ RealIntegral (realTailShift realPrimeGapTail 1 3) ∧
    primeGap0 4 = 2 ∧ primeGap0 3 = 4 := by
  sorry
end PalomarCorpus.E251.PaperStatementsP

namespace PalomarCorpus.E251.PaperStatementsB
open Filter
open Topology
/-- States long251:res:one-tail-certificate from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.one_tail_signed_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_tail_signed_certificate (D D' : ℝ) (s A B Q : ℤ)
    (hs : s = -1 ∨ s = 1) (hQ : 0 < Q) (hB : 0 ≤ B)
    (hstep : D' = 2 * D - (2 * s : ℤ))
    (herr : |(Q : ℝ) * D - A| ≤ B)
    (hlo : 2 * s * A - Q > 2 * B) (hhi : Q - s * A > B) :
    ((1/2 : ℝ) < (s : ℝ)*D ∧ (s : ℝ)*D < 1) ∧ |D'| < 1 ∧
      D ∉ Set.range ((↑) : ℤ → ℝ) ∧ D' ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
end PalomarCorpus.E251.PaperStatementsB

namespace PalomarCorpus.E251.ExactDenominatorFloors
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E251_02.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)
/-- Any positive denominator representing either the dyadic prime series or the dyadic prime-gap series is at least 2^589 and strictly exceeds 10^177. -/
theorem denominator_floor_both (a : ℤ) (b : ℕ) (hb : 0 < b) :
    ((∑' n, primeDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) ∧
    ((∑' n, primeGapDyadicTerm n) = a / b → 2 ^ 589 ≤ b ∧ 10 ^ 177 < b) := by
  sorry
end PalomarCorpus.E251.ExactDenominatorFloors

namespace PalomarCorpus.E251.PaperStatementsF
open scoped BigOperators
open Finset
/-- States long251:res:denominatorfloor from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.denominator_floor_decimal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem denominator_floor_decimal : (10 ^ 177 : ℕ) < 2 ^ 589 := by
  sorry
end PalomarCorpus.E251.PaperStatementsF
