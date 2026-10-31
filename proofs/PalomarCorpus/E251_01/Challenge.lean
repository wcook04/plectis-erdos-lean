/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #251, record sections 2 to 5: sparse congruence-preserving perturbations; summation by parts, with the endpoint retained; the tail recurrence and the exact criteria

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #251, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #251 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Topology
open Finset
open Filter Topology
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E251_01.Shared
/-- The same dyadic tail recurrence with integer digits `g` for a real sequence: `T (N + 1) = 2 * T N - g (N + 1)` at every index `N`, with the integer digit cast into the reals. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- Uniformly in the starting index, every sufficiently long interval contains at most a 1/R proportion of S, for each positive integer R. -/
noncomputable def UpperBanachZero (S : Set ℕ) : Prop := by
  classical
  exact ∀ R : ℕ, 0 < R → ∃ L₀ : ℕ, ∀ a L : ℕ, L₀ ≤ L →
    R * ((Finset.Ico a (a + L)).filter (fun n => n ∈ S)).card ≤ L
/-- The shift of length `h` at basepoint `N` of a real orbit, namely the difference `T (N + h) - T N`. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
end PalomarCorpus.E251_01.Shared

namespace PalomarCorpus.E251.PaperStatementsA
open Filter
open Topology
open Finset
/-- Local copy of ErdosProblems.Erdos251.PaperR11.GrowingBlocks.testMean, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def testMean {α : Type*} (a : ℕ → α) (X m : ℕ)
    (Φ : ℕ → (Fin m → α) → ℝ) : ℝ :=
  (∑ N ∈ Ico X (2 * X), Φ N (fun i => a (N + i.val))) / X
/-- States long251:res:sparse-rationalisation from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.bounded_test_finite_coupling in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bounded_test_finite_coupling {α : Type*} (a b : ℕ → α)
    (X m : ℕ) (S : Finset ℕ)
    (hS : ∀ N ∈ Ico X (2*X), ∀ i : Fin m,
      a (N+i.val) ≠ b (N+i.val) → N+i.val ∈ S)
    (B : ℝ) (hB : 0 ≤ B) (Φ : ℕ → (Fin m → α) → ℝ)
    (ha : ∀ N ∈ Ico X (2*X), |Φ N (fun i => a (N+i.val))| ≤ B)
    (hb : ∀ N ∈ Ico X (2*X), |Φ N (fun i => b (N+i.val))| ≤ B) :
    |testMean a X m Φ - testMean b X m Φ| ≤ 2*B*(m : ℝ)*S.card/X := by
  sorry
end PalomarCorpus.E251.PaperStatementsA

namespace PalomarCorpus.E251.UniformSparseRationalisation
open Filter Topology
open scoped BigOperators
open Finset
export PalomarCorpus.E251_01.Shared (UpperBanachZero)
/-- The starting indices in I whose length-m block lies in the specified event. -/
noncomputable def eventStarts {α : Type*} (a : ℕ → α) (I : Finset ℕ) (m : ℕ)
    (event : Set (Fin m → α)) : Finset ℕ := by
  classical
  exact I.filter (fun N => (fun i : Fin m => a (N + i.val)) ∈ event)
/-- The fraction, normalized by X, of starts in [X, 2X) whose length-m block lies in the event. -/
noncomputable def eventFrequency {α : Type*} (a : ℕ → α) (X m : ℕ)
    (E : Set (Fin m → α)) : ℝ := (eventStarts a (Ico X (2 * X)) m E).card / (X : ℝ)
/-- The supremum over block events of the absolute difference of their frequencies for the two words. -/
noncomputable def blockTV {α : Type*} (a b : ℕ → α) (X m : ℕ) : ℝ :=
  sSup (Set.range (fun E : Set (Fin m → α) => |eventFrequency a X m E - eventFrequency b X m E|))
/-- The envelope (log(n + 3))^α. -/
noncomputable def polylog (α : ℝ) (n : ℕ) : ℝ := (Real.log ((n : ℝ) + 3)) ^ α
/-- The smoothed iterated logarithm log(log(n + 3)). -/
noncomputable def iterlog (n : ℕ) : ℝ := Real.log (Real.log ((n : ℝ) + 3))
/-- The elements of S in the half-open interval [a, a + L). -/
noncomputable def supportSlice (S : Set ℕ) (a L : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ico a (a + L)).filter (fun n => n ∈ S)
/-- One support, target interval, counting constant and divisibility-cutoff function work for every target in the interval. The support has zero upper Banach density, satisfies the stated quantitative counting bound, and uniformly controls growing-block variation for every word changed only there; the constructed perturbations satisfy the polylogarithmic envelope, common divisibility cutoffs and exact finite-window variation bound. -/
theorem polylogarithmic_word_interval_uniform (a : ℕ → ℕ) {A ε : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (hε : 0 < ε) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u C : ℝ, ∃ Nq : ℕ → ℕ,
      (S ⊆ Set.Ici K) ∧
      UpperBanachZero (S) ∧
      A < l ∧ l < u ∧ 0 < C ∧
      (∃ X₀ : ℕ, ∀ X L : ℕ, X₀ ≤ X → L ≤ 2 * X →
        ((supportSlice S X L).card : ℝ) ≤ C * X / iterlog X) ∧
      (∀ m : ℕ → ℕ,
        Tendsto (fun X => (m X : ℝ) / Real.log (Real.log (X : ℝ))) atTop (𝓝 0) →
        ∀ η : ℝ, 0 < η → ∀ᶠ X : ℕ in atTop,
          ∀ b : ℕ → ℕ,
            (∀ n, a n ≠ b n → n ∈ S) →
            blockTV a b X (m X) < η) ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ polylog ε n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        (∀ n < K, a n + e n = a n) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r ∧
        ∀ X m : ℕ, blockTV a (fun n => a n + e n) X m ≤
          (m : ℝ) * (supportSlice S X (X + m)).card / X := by
  sorry
/-- For every envelope tending to infinity, one support of zero upper Banach density, one target interval and one divisibility-cutoff function work for every target in that interval; the positive perturbations eventually obey the envelope and preserve the prescribed initial segment. -/
theorem arbitrary_word_sparse_rationalisation_uniform (a : ℕ → ℕ) {A : ℝ}
    (ha : HasSum (fun n => (a n : ℝ) / 2 ^ (n + 1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) :
    ∃ S : Set ℕ, ∃ l u : ℝ, ∃ Nq : ℕ → ℕ,
      S ⊆ Set.Ici K ∧ UpperBanachZero S ∧ A < l ∧ l < u ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ S) ∧
        (∀ᶠ n : ℕ in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        HasSum (fun n => ((a n + e n : ℕ) : ℝ) / 2 ^ (n + 1)) r := by
  sorry
end PalomarCorpus.E251.UniformSparseRationalisation

namespace PalomarCorpus.E251.PaperStatementsI
open Filter
open Topology
open Finset
export PalomarCorpus.E251_01.Shared (UpperBanachZero)
/-- A level-k step. The square is convenient; sharp constants are not claimed. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.gap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def gap (k : ℕ) : ℕ := (k + 4) ^ 2
/-- A level-k capacity, allowing two successive modulus upgrades. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.amplitude, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def amplitude (k : ℕ) : ℕ := 4 * (k + 3).factorial * 2 ^ gap k
/-- A stage is allowed only after its entire future budget is available. The additional linear bound ensures geometric summability independently of how rapidly the supplied envelope grows. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.Ready, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Ready (f : ℕ → ℝ) (n k : ℕ) : Prop :=
  ∀ m, n ≤ m → (amplitude k : ℝ) ≤ f m ∧ amplitude k ≤ m + 1
/-- Upgrade by one level exactly when the future budget allows it. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.upgrade, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def upgrade (f : ℕ → ℝ) (n k : ℕ) : ℕ := by
  classical
  exact if Ready f n (k + 1) then k + 1 else k
/-- State = (centre, level), with no assumed rate for the envelope. Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.state, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def state (f : ℕ → ℝ) (start : ℕ) : ℕ → ℕ × ℕ
  | 0 => (start, 0)
  | j + 1 =>
      let s := state f start j
      let n := s.1 + gap s.2
      (n, upgrade f n s.2)
/-- Local copy of ErdosProblems.Erdos251.PaperR8.SparseSchedule.centre, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centre (f : ℕ → ℝ) (start j : ℕ) : ℕ := (state f start j).1
/-- States long251:res:local-targets from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.local_target_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem local_target_interval (a : ℕ → ℕ) {A η : ℝ}
    (ha : HasSum (fun n => (a n : ℝ)/2^(n+1)) A)
    (f : ℕ → ℝ) (hf : Tendsto f atTop atTop) (K : ℕ) (hη : 0 < η) :
    ∃ start : ℕ, ∃ l u : ℝ, ∃ Nq : ℕ → ℕ,
      (Set.range (centre f start) ⊆ Set.Ici K) ∧
      UpperBanachZero (Set.range (centre f start)) ∧
      A < l ∧ l < u ∧ u < A+η ∧
      ∀ r : ℝ, l ≤ r → r ≤ u → ∃ e : ℕ → ℕ,
        (∀ n, e n ≠ 0 → n ∈ Set.range (centre f start)) ∧
        (∀ n < K, a n+e n = a n) ∧
        (∀ᶠ n in atTop, (e n : ℝ) ≤ f n) ∧
        (∀ q : ℕ, 0 < q → ∀ n, Nq q ≤ n →
          q ∣ e n ∧ q ∣ ∑ i ∈ range n, e i) ∧
        HasSum (fun n => ((a n+e n : ℕ) : ℝ)/2^(n+1)) r := by
  sorry
end PalomarCorpus.E251.PaperStatementsI

namespace PalomarCorpus.E251.PaperStatementsG
open scoped BigOperators
export PalomarCorpus.E251_01.Shared (RealDyadicTailRecurrence realTailShift)
/-- A real number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RealIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- Cofinal failure of integral shifts for every fixed positive length. Local copy of ErdosProblems.Erdos251.CofinalNonintegralTailShifts, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)
/-- Finite dyadic partial sum of the forward differences of a sequence. Local copy of ErdosProblems.Erdos251.dyadicDifferencePartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicDifferencePartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (P (i + 1) - P i) / 2 ^ (i + 1)
/-- Finite zero-based dyadic partial sum of a rational sequence. Local copy of ErdosProblems.Erdos251.dyadicPartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicPartialSumQ (P : ℕ → ℚ) (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, P i / 2 ^ (i + 1)
/-- Zero-based prime enumeration. Local copy of ErdosProblems.Erdos251.prime0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- The term with denominator `2^n` used by the displayed formal conjecture. Local copy of ErdosProblems.Erdos251.primeDisplayedDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeDisplayedDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ n
/-- The real term in the normalized zero-based prime series. Local copy of ErdosProblems.Erdos251.primeDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeDyadicTerm (n : ℕ) : ℝ :=
  (prime0 n : ℝ) / 2 ^ (n + 1)
/-- Zero-based consecutive prime gap. Local copy of ErdosProblems.Erdos251.primeGap0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
/-- The real term in the corresponding consecutive-prime-gap series. Local copy of ErdosProblems.Erdos251.primeGapDyadicTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGapDyadicTerm (n : ℕ) : ℝ :=
  (primeGap0 n : ℝ) / 2 ^ (n + 1)
/-- Finite dyadic partial sum of the actual consecutive prime gaps. Local copy of ErdosProblems.Erdos251.primeGapPartialSumQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGapPartialSumQ (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n, (primeGap0 i : ℚ) / 2 ^ (i + 1)
/-- States long251:res:infinite, res:infinite, res:irr-equivalence from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.infinite_prime_gap_identity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem infinite_prime_gap_identity :
    Summable primeDyadicTerm ∧ Summable primeGapDyadicTerm ∧
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n := by
  sorry
/-- States long251:res:irr-equivalence, res:irr-equivalence from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.irrationality_reformulation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrationality_reformulation :
    (Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) ∧
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n ∧
    (Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n)) := by
  sorry
/-- States long251:res:escape-irrational, res:escape-irrational from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.rationality_classification in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rationality_classification {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) :
    (¬ Irrational (T 0) ↔
      ∃ h N : ℕ, 0 < h ∧ RealIntegral (realTailShift T h N)) ∧
    (¬ Irrational (T 0) ↔
      ∃ h N₀ : ℕ, 0 < h ∧
        ∀ N, N₀ ≤ N → RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔
      ∀ h : ℕ, 0 < h → ∀ N, ¬ RealIntegral (realTailShift T h N)) ∧
    (Irrational (T 0) ↔ CofinalNonintegralTailShifts T) := by
  sorry
/-- States long251:res:abel from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.dyadicPartialSumQ_eq_start_add_differences in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicPartialSumQ_eq_start_add_differences
    (P : ℕ → ℚ) (n : ℕ) :
    dyadicPartialSumQ P (n + 1) =
      P 0 + dyadicDifferencePartialSumQ P n - P n / 2 ^ (n + 1) := by
  sorry
/-- States long251:res:parts from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.prime0_dyadic_summation_by_parts in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prime0_dyadic_summation_by_parts (n : ℕ) :
    dyadicPartialSumQ (fun i => (prime0 i : ℚ)) (n + 1) =
      2 + primeGapPartialSumQ n - (prime0 n : ℚ) / 2 ^ (n + 1) := by
  sorry
end PalomarCorpus.E251.PaperStatementsG

namespace PalomarCorpus.E251.PaperStatementsH
open scoped BigOperators
export PalomarCorpus.E251_01.Shared (RealDyadicTailRecurrence realTailShift)
/-- The integer block accumulated through `h` dyadic tail steps beginning at index `N`. Recursively, this is `g (N+1) * 2^(h-1) + ⋯ + g (N+h)`. Local copy of ErdosProblems.Erdos251.dyadicTailBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dyadicTailBlock g N h + g (N + h + 1)
/-- States long251:res:block from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.real_block_identity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_block_identity {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (N h : ℕ) :
    T (N + h) = 2 ^ h * T N - dyadicTailBlock g N h ∧
    realTailShift T h N = ((2 ^ h : ℝ) - 1) * T N - dyadicTailBlock g N h := by
  sorry
end PalomarCorpus.E251.PaperStatementsH

namespace PalomarCorpus.E251.PaperStatementsC
open Filter
open Finset
open scoped BigOperators
open scoped Topology
/-- Local copy of ErdosProblems.Erdos251.PaperCompleteR20.realDyadicTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realDyadicTail (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, a (N + j + 1) / 2 ^ (j + 1)
/-- States long251:res:true-tail, res:true-tail from the long record and the short record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.real_dyadic_orbit_eq_true_tail_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_dyadic_orbit_eq_true_tail_iff (a U : ℕ → ℝ)
    (habs : Summable (fun j : ℕ => |a (j + 1)| / (2 : ℝ) ^ (j + 1)))
    (hrec : ∀ N, U (N + 1) = 2 * U N - a (N + 1)) :
    (∀ N, U N = realDyadicTail a N) ↔
      Tendsto (fun N : ℕ => U N / 2 ^ N) atTop (𝓝 0) := by
  sorry
end PalomarCorpus.E251.PaperStatementsC
