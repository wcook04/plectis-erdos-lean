/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #251, record sections 8.2 to 8.6: algebraic nonconcentration survives the rationalising perturbation; the two-window event has density zero; recurring gap values differing by two do not suffice

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #251, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #251 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Topology
open Finset
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E251_03.Shared
/-- A set of natural numbers has density zero when for every positive real `ε` all sufficiently large `N` have fewer than `ε * N` elements below `N`. -/
noncomputable def ZeroDensity (s : Set ℕ) : Prop := by
  classical
  exact ∀ ε : ℝ, 0 < ε → ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
    (((range N).filter (fun n => n ∈ s)).card : ℝ) < ε * N
/-- Fixed-block polynomial nonconcentration for an integer word. Local copy of ErdosProblems.Erdos251.PaperR7.FixedBlockNonconcentration, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FixedBlockNonconcentration (a : ℕ → ℤ) : Prop :=
  ∀ m : ℕ, 0 < m → ∀ F : MvPolynomial (Fin m) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval (fun i : Fin m => a (n + i.val)) F = 0}
/-- The zero-based enumeration of the primes in increasing order, so that `prime0 0 = 2`, `prime0 1 = 3`, and `prime0 n` is the `(n + 1)`st prime. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- The `n`th consecutive prime gap in the zero-based indexing, `prime0 (n + 1) - prime0 n`. The subtraction is truncated subtraction of natural numbers, which agrees with the ordinary difference because the primes increase; the first values are 1, 2, 2, 4, 2, 4. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
end PalomarCorpus.E251_03.Shared

namespace PalomarCorpus.E251.PaperStatementsR
open Filter
open Topology
open Finset
open scoped BigOperators
export PalomarCorpus.E251_03.Shared (prime0 primeGap0)
/-- Four distinct primes with two outer gaps differing by r. Local copy of ErdosProblems.Erdos251.PaperR9.ShiftCounting.quadCandidates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def quadCandidates (N H : ℕ) (r : ℤ) : Finset ((ℕ × ℕ) × ℕ) := by
  classical
  exact (((range (prime0 N)).product (range (H + 1))).product (range (H + 1))).filter
    (fun z =>
      0 < z.1.2 ∧ z.1.2 < z.2 ∧ 0 < (z.1.2 : ℤ) + r ∧
      Nat.Prime z.1.1 ∧ Nat.Prime (z.1.1 + z.1.2) ∧ Nat.Prime (z.1.1 + z.2) ∧
      Nat.Prime (((z.1.1 : ℤ) + z.2 + z.1.2 + r).toNat))
/-- Local copy of ErdosProblems.Erdos251.PaperR9.ShiftCounting.shiftedMatches, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftedMatches (h N : ℕ) (r : ℤ) : Finset ℕ := by
  classical
  exact (range N).filter (fun n => (primeGap0 (n + h) : ℤ) - primeGap0 n = r)
/-- States long251:res:shiftedcount from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR9.ShiftCounting.shifted_count_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem shifted_count_bound (h N H : ℕ) (hh : 2 ≤ h) (r : ℤ) :
    (H + 1) * (shiftedMatches h N r).card ≤
      (h + 1) * prime0 (N + (h + 1)) + (H + 1) * (quadCandidates N H r).card := by
  sorry
end PalomarCorpus.E251.PaperStatementsR

namespace PalomarCorpus.E251.PaperStatementsF
open scoped BigOperators
open Finset
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity)
/-- States long251:res:nonconcentration from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.finite_perturbation_stability in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_perturbation_stability
    (a b : ℕ → ℤ) (E : Finset ℤ)
    (ha : FixedBlockNonconcentration a)
    (hE : ∀ n, b n - a n ∈ E) :
    FixedBlockNonconcentration b := by
  sorry
end PalomarCorpus.E251.PaperStatementsF

namespace PalomarCorpus.E251.PaperStatementsZA
open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Topology
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity prime0 primeGap0)
/-- States long251:res:nonconc-primes from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR21.nonconcentration_does_not_force_irrationality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem nonconcentration_does_not_force_irrationality
    (M : ℕ) (hM : 0 < M) (K : ℕ)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ)))
    (hPNT : Tendsto (fun n : ℕ => (prime0 n : ℝ) / ((n : ℝ) * Real.log n))
      atTop (𝓝 1)) :
    ∃ (b : ℕ → ℕ) (q : ℚ),
      HasSum (fun n => (b n : ℝ) / 2 ^ (n + 1)) (q : ℝ) ∧
      (∀ n < K, b n = primeGap0 n) ∧
      (∀ n, (b n : ℤ) - primeGap0 n = 0 ∨ (b n : ℤ) - primeGap0 n = (M : ℤ)) ∧
      (∀ n, primeGap0 n ≤ b n) ∧
      (∀ n, b n % M = primeGap0 n % M) ∧
      FixedBlockNonconcentration (fun n => (b n : ℤ)) ∧
      (∀ n, prime0 n ≤ 2 + ∑ i ∈ range n, b i) ∧
      (∀ n, 2 + ∑ i ∈ range n, b i ≤ prime0 n + M * n) ∧
      Tendsto (fun n : ℕ => ((2 + ∑ i ∈ range n, b i : ℕ) : ℝ) / ((n : ℝ) * Real.log n))
        atTop (𝓝 1) := by
  sorry
end PalomarCorpus.E251.PaperStatementsZA

namespace PalomarCorpus.E251.PaperStatementsK
open Filter
open Topology
open Finset
open scoped BigOperators
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity)
/-- States long251:res:sparse-nonconcentration from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.sparse_nonconcentration in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sparse_nonconcentration (a b : ℕ → ℤ) (S : Set ℕ)
    (hS : ZeroDensity S) (hab : ∀ n, n ∉ S → a n = b n)
    (ha : FixedBlockNonconcentration a) : FixedBlockNonconcentration b := by
  sorry
end PalomarCorpus.E251.PaperStatementsK

namespace PalomarCorpus.E251.PaperStatementsX
open Filter
open Topology
open Finset
open scoped BigOperators
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity prime0 primeGap0)
/-- Event counts with classical membership made explicit in the definition. Local copy of ErdosProblems.Erdos251.PaperR7.eventStarts, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def eventStarts {α : Type*} (a : ℕ → α) (I : Finset ℕ) (m : ℕ)
    (event : Set (Fin m → α)) : Finset ℕ := by
  classical
  exact I.filter (fun N => (fun i : Fin m => a (N + i.val)) ∈ event)
/-- Local copy of ErdosProblems.Erdos251.PaperR11.GrowingBlocks.eventFrequency, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def eventFrequency {α : Type*} (a : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : ℝ := (eventStarts a (Ico X (2 * X)) m E).card / (X : ℝ)
/-- Local copy of ErdosProblems.Erdos251.PaperR11.GrowingBlocks.blockTV, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def blockTV {α : Type*} (a b : ℕ → α) (X m : ℕ) : ℝ :=
  sSup (Set.range (fun E : Set (Fin m → α) => |eventFrequency a X m E - eventFrequency b X m E|))
/-- Local copy of ErdosProblems.Erdos251.PaperR11.PerturbationGrowth.scale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scale (n : ℕ) : ℝ := (n : ℝ) * Real.log (n : ℝ)
/-- Classical PNT input only for the ORIGINAL nth prime. Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.PrimeNumberTheorem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PrimeNumberTheorem : Prop :=
  Tendsto (fun n => (prime0 n : ℝ) / scale n) atTop (𝓝 1)
/-- Schlage-Puchta, Lemma 4, in zero-based consecutive-prime-gap notation. Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.SchlagePuchtaLemma4, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SchlagePuchtaLemma4 : Prop :=
  ∀ k : ℕ, ∀ F : MvPolynomial (Fin (k + 1)) ℤ, F ≠ 0 →
    ZeroDensity {n | MvPolynomial.eval
      (fun i : Fin (k + 1) => (primeGap0 (n + i.val) : ℤ)) F = 0}
/-- Local copy of ErdosProblems.Erdos251.PaperR11.PrimeSource.cumulative, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cumulative (b : ℕ → ℕ) (n : ℕ) : ℕ := 2 + ∑ i ∈ range n, b i
/-- Local copy of ErdosProblems.Erdos251.PaperR11.SparsePolylog.polylog, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polylog (α : ℝ) (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 3)) ^ α
/-- States long251:res:jointcountermodel from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR21.long_joint_prime_gap_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem long_joint_prime_gap_countermodel
    (hSP : SchlagePuchtaLemma4) (hPNT : PrimeNumberTheorem)
    (K : ℕ) {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ e : ℕ → ℕ, ∃ r : ℚ, ∃ C : ℝ, 0 < C ∧
      (∀ n, n < K → e n = 0) ∧
      HasSum (fun n => ((primeGap0 n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) (r : ℝ) ∧
      (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
      (∀ q : ℕ, 0 < q → ∀ᶠ n : ℕ in atTop,
        primeGap0 n + e n ≡ primeGap0 n [MOD q] ∧
        cumulative (fun i => primeGap0 i + e i) n ≡ prime0 n [MOD q]) ∧
      FixedBlockNonconcentration (fun n => ((primeGap0 n + e n : ℕ) : ℤ)) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        Tendsto (fun X =>
          blockTV primeGap0 (fun n => primeGap0 n + e n) X (m X)) atTop (𝓝 0)) ∧
      (∀ n, prime0 n ≤ cumulative (fun i => primeGap0 i + e i) n) ∧
      (∀ᶠ n : ℕ in atTop,
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) - prime0 n
          ≤ C * ((n : ℝ) * polylog ε n / Real.log (Real.log (n : ℝ)))) ∧
      Tendsto (fun n =>
        (cumulative (fun i => primeGap0 i + e i) n : ℝ) / scale n) atTop (𝓝 1) := by
  sorry
end PalomarCorpus.E251.PaperStatementsX

namespace PalomarCorpus.E251.PaperStatementsY
open scoped BigOperators
open Filter
open Topology
open Finset
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity prime0 primeGap0)
/-- Local copy of ErdosProblems.Erdos251.PaperR11.Nonconcentration.shift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shift (T : ℕ → ℝ) (h N : ℕ) : ℝ := T (N + h) - T N
/-- The real term in the corresponding consecutive-prime-gap series. Local copy of ErdosProblems.Erdos251.primeGapDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)
/-- Finite dyadic partial sum of the actual consecutive prime gaps. Local copy of ErdosProblems.Erdos251.primeGapPartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)
/-- The genuine scaled tail after the first `N+1` prime-gap terms. Local copy of ErdosProblems.Erdos251.realPrimeGapTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realPrimeGapTail (N : ℕ) : ℝ :=
  2 ^ (N + 1) *
    ((∑' n : ℕ, primeGapDyadicTerm n) - (primeGapPartialSumQ (N + 1) : ℝ))
/-- States long251:res:sparse from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_equal_shift_zeroDensity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime_gap_equal_shift_zeroDensity (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | primeGap0 (N + h + 1) = primeGap0 (N + 1)} := by
  sorry
/-- States long251:res:sparse from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR21.prime_gap_two_window_sparse in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime_gap_two_window_sparse (h : ℕ) (hh : 0 < h)
    (hSP : FixedBlockNonconcentration (fun n => (primeGap0 n : ℤ))) :
    ZeroDensity {N | 1 ≤ N ∧
        (-1 < shift realPrimeGapTail h N ∧ shift realPrimeGapTail h N < 1) ∧
        (-1 < shift realPrimeGapTail h (N + 1) ∧
          shift realPrimeGapTail h (N + 1) < 1) ∧
        (primeGap0 (N + h + 1) : ℤ) ≠ (primeGap0 (N + 1) : ℤ)} ∧
      ZeroDensity {N | (primeGap0 (N + h + 1) : ℤ) = (primeGap0 (N + 1) : ℤ)} := by
  sorry
end PalomarCorpus.E251.PaperStatementsY

namespace PalomarCorpus.E251.PaperStatementsA
open Filter
open Topology
open Finset
/-- States long251:res:polignacfail from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR8.LogCarry.exists_logarithmic_recurring_values_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_logarithmic_recurring_values_countermodel :
    ∃ a U : ℕ → ℤ,
      let P : ℕ → ℤ := fun n => 3 + ∑ j ∈ range n, a (j + 1);
      (∀ n, 1 ≤ n → 0 < a n ∧ (2 : ℤ) ∣ a n) ∧
      (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧ a i = 2 ∧ a j = 4) ∧
      (∀ B : ℤ, ∀ N : ℕ, ∃ n, N ≤ n ∧ B < a n) ∧
      (∀ h : ℕ, 0 < h → ¬ ∃ N₀, ∀ n, N₀ ≤ n → a (n + h) = a n) ∧
      (∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, 2 ≤ n → (a n : ℝ) ≤ C * Real.log (n : ℝ)) ∧
      HasSum (fun j : ℕ => (a (j + 1) : ℝ) / 2 ^ (j + 1)) 6 ∧
      (∀ N, HasSum (fun j : ℕ => (a (N + j + 1) : ℝ) / 2 ^ (j + 1)) (U N : ℝ)) ∧
      (∀ N h, ∃ z : ℤ,
        (∑' j : ℕ, (a (N + h + j + 1) : ℝ) / 2 ^ (j + 1)) -
        (∑' j : ℕ, (a (N + j + 1) : ℝ) / 2 ^ (j + 1)) = z) ∧
      StrictMono P ∧ (∀ n, ∃ z : ℤ, P n = 2 * z + 1) ∧
      Tendsto (fun n : ℕ => (P n : ℝ) / ((n : ℝ) * Real.log n)) atTop (𝓝 1) := by
  sorry
end PalomarCorpus.E251.PaperStatementsA

namespace PalomarCorpus.E251.PaperStatementsG
open scoped BigOperators
/-- Abstract dyadic tail recurrence with integer digits. The rational candidate state below is an exact actual-gap instance; identifying a candidate with the genuine infinite sum remains analytic. Local copy of ErdosProblems.Erdos251.DyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A rational number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RatIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- The coefficient emitted by an unrestricted integer carry. Local copy of ErdosProblems.Erdos251.carryCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryCoeff (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  2 * K n - K (n + 1)
/-- The finite dyadic series emitted by `carryCoeff`. Local copy of ErdosProblems.Erdos251.carryPartialSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryPartialSum (K : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, carryCoeff K i / 2 ^ (i + 1)
/-- A positive even polynomial gap word. It is not the actual prime-gap word; it is an exact stress test for attempts using only coarse gap properties. Local copy of ErdosProblems.Erdos251.polynomialGapWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialGapWord (n : ℕ) : ℤ :=
  (2 * (n ^ 2 + 4 * n + 2) : ℕ)
/-- The rational polynomial tail orbit paired with `polynomialGapWord`. Local copy of ErdosProblems.Erdos251.polynomialTailOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialTailOrbit (n : ℕ) : ℚ :=
  (2 * (n + 4) ^ 2 : ℕ)
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
/-- States long251:res:polynomialcountermodel from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.polynomial_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem polynomial_countermodel :
    (∀ n, 0 < polynomialGapWord n) ∧
    (∀ n, ∃ k : ℤ, polynomialGapWord n = 2 * k) ∧
    StrictMono polynomialGapWord ∧
    DyadicTailRecurrence polynomialGapWord polynomialTailOrbit ∧
    (∀ h N, RatIntegral (tailShift polynomialTailOrbit h N)) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n = 4 * (n : ℤ) + 10) ∧
    (∀ n, polynomialGapWord (n + 1) - polynomialGapWord n ≠ 2 ∧
      polynomialGapWord (n + 1) - polynomialGapWord n ≠ -2) ∧
    HasSum (fun n : ℕ => (polynomialGapWord (n + 1) : ℝ) / 2 ^ (n + 1)) 32 := by
  sorry
/-- States long251:res:telescope from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.carryPartialSum_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem carryPartialSum_eq (K : ℕ → ℚ) (n : ℕ) :
    carryPartialSum K n = K 0 - K n / 2 ^ n := by
  sorry
end PalomarCorpus.E251.PaperStatementsG
