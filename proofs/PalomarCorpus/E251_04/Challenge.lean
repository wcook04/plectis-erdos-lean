/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #251, record sections D to E: further criteria, examples and computational details; arithmetic-progression reformulations of integrality

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #251, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #251 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Filter
open Topology

namespace PalomarCorpus.E251_04.Shared
/-- The dyadic tail recurrence with integer digits `g`: a rational sequence `T` satisfies `T (N + 1) = 2 * T N - g (N + 1)` at every index `N`, with the integer digit cast into the rationals. This is the relation obeyed by the rescaled tails `T N = sum over j at least 1 of g (N + j) / 2 ^ j` of a dyadic series with integer coefficients. -/
noncomputable def DyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℚ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- A rational number is integral when it is the image of an integer under the cast from the integers to the rationals, equivalently when its reduced denominator is 1. -/
noncomputable def RatIntegral (x : ℚ) : Prop :=
  ∃ z : ℤ, x = z
/-- A real number is integral when it equals the cast of an integer. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
/-- The shift of length `h` at basepoint `N` of a real orbit, namely the difference `T (N + h) - T N`. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- Difference between two tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.tailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailShift (T : ℕ → ℚ) (h N : ℕ) : ℚ :=
  T (N + h) - T N
end PalomarCorpus.E251_04.Shared

namespace PalomarCorpus.E251.PaperStatementsG
open scoped BigOperators
export PalomarCorpus.E251_04.Shared (DyadicTailRecurrence RatIntegral tailShift)
/-- States long251:xr:totient from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.tailShift_integral_totient_of_odd_den in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailShift_integral_totient_of_odd_den
    {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) (N : ℕ)
    (hodd : Odd (T N).den) :
    RatIntegral (tailShift T (T N).den.totient N) := by
  sorry
end PalomarCorpus.E251.PaperStatementsG

namespace PalomarCorpus.E251.PaperStatementsM
open scoped BigOperators
export PalomarCorpus.E251_04.Shared (DyadicTailRecurrence RatIntegral RealIntegral realTailShift tailShift)
/-- A bound is dyadically dominated when every fixed rational denominator is eventually overwhelmed by the depth scale. Polynomial bounds have this property; the definition isolates exactly the growth input used below. Local copy of ErdosProblems.Erdos251.DyadicScaleDominates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicScaleDominates (bound : ℕ → ℚ) : Prop :=
  ∀ N q : ℕ, 0 < q → ∃ r : ℕ,
    2 * bound (N + r) * q < 2 ^ r
/-- `x` lies in the affine class `-c` modulo `2^(r+1)`. Local copy of ErdosProblems.Erdos251.RatAffinePowTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatAffinePowTwo (x : ℚ) (c : ℤ) (r : ℕ) : Prop :=
  ∃ z : ℤ, x = ((((2 : ℤ) ^ (r + 1)) * z - c : ℤ) : ℚ)
/-- A rational that is the cast of an even integer. Local copy of ErdosProblems.Erdos251.RatEvenIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RatEvenIntegral (x : ℚ) : Prop := ∃ k : ℤ, x = ((2 * k : ℤ) : ℚ)
/-- Real-valued version of the dyadic tail recurrence. Local copy of ErdosProblems.Erdos251.RealDyadicTailRecurrence, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealDyadicTailRecurrence (g : ℕ → ℤ) (T : ℕ → ℝ) : Prop :=
  ∀ N, T (N + 1) = 2 * T N - g (N + 1)
/-- The integer block accumulated through `h` dyadic tail steps beginning at index `N`. Recursively, this is `g (N+1) * 2^(h-1) + ⋯ + g (N+h)`. Local copy of ErdosProblems.Erdos251.dyadicTailBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicTailBlock (g : ℕ → ℤ) (N : ℕ) : ℕ → ℤ
  | 0 => 0
  | h + 1 => 2 * dyadicTailBlock g N h + g (N + h + 1)
/-- The digit sequence governing the fixed `h`-shift cocycle. Local copy of ErdosProblems.Erdos251.shiftDigit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftDigit (g : ℕ → ℤ) (h n : ℕ) : ℤ := g (n + h) - g n
/-- States long251:xr:propagate from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.realTailShift_integral_add in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem realTailShift_integral_add
    {g : ℕ → ℤ} {T : ℕ → ℝ}
    (hrec : RealDyadicTailRecurrence g T) (h N : ℕ)
    (hInt : RealIntegral (realTailShift T h N)) :
    ∀ k : ℕ, RealIntegral (realTailShift T h (N + k)) := by
  sorry
/-- States eq:affinecofinal, eq:affinecollapse, eq:dyadicscale from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.affine_circularity_bundle in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem affine_circularity_bundle {g : ℕ → ℤ} {T : ℕ → ℚ}
    (hrec : DyadicTailRecurrence g T) :
    (∀ h N r : ℕ,
      RatAffinePowTwo (tailShift T h (N + r))
        (dyadicTailBlock (shiftDigit g h) N r) r ↔
      RatEvenIntegral (tailShift T h N)) ∧
    (∀ h : ℕ,
      (∀ N, ∃ k : ℤ, g (N + h + 1) - g (N + 1) = 2 * k) →
      ((∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧
        ¬ RatAffinePowTwo (tailShift T h (N + r))
          (dyadicTailBlock (shiftDigit g h) N r) r) ↔
        ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))) ∧
    (∀ (h : ℕ) (bound : ℕ → ℚ),
      (∀ N, |tailShift T h N| ≤ bound N) → DyadicScaleDominates bound →
      ((∀ N₀ : ℕ, ∃ N r : ℕ, N₀ < N ∧ ∀ z : ℤ,
        bound (N + r) <
          |(dyadicTailBlock (shiftDigit g h) N r : ℚ) - 2 ^ r * (z : ℚ)|) ↔
        ¬ ∃ N₀, ∀ N, N₀ ≤ N → RatIntegral (tailShift T h N))) := by
  sorry
end PalomarCorpus.E251.PaperStatementsM

namespace PalomarCorpus.E251.PaperStatementsN
open Filter
open Topology
open scoped BigOperators
export PalomarCorpus.E251_04.Shared (RealIntegral realTailShift)
/-- Cofinal failure of integral shifts for every fixed positive length. Local copy of ErdosProblems.Erdos251.CofinalNonintegralTailShifts, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CofinalNonintegralTailShifts (T : ℕ → ℝ) : Prop :=
  ∀ h, 0 < h → ∀ N₀, ∃ N, N₀ ≤ N ∧
    ¬RealIntegral (realTailShift T h N)
/-- Euclidean distance to the complete integer lattice. Local copy of ErdosProblems.Erdos251.PaperR7.integerDistance, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerDistance (x : ℝ) : ℝ :=
  Metric.infDist x (Set.range (fun z : ℤ => (z : ℝ)))
/-- Local copy of ErdosProblems.Erdos251.PaperR7.majorantRemainderTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def majorantRemainderTerm (M : ℕ → ℝ) (h N L j : ℕ) : ℝ :=
  (M (N + h + L + j + 1) + M (N + L + j + 1)) / 2 ^ (L + j + 1)
/-- Local copy of ErdosProblems.Erdos251.PaperR7.majorantRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def majorantRemainder (M : ℕ → ℝ) (h N L : ℕ) : ℝ :=
  ∑' j : ℕ, majorantRemainderTerm M h N L j
/-- Zero-based prime enumeration. Local copy of ErdosProblems.Erdos251.prime0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prime0 (n : ℕ) : ℕ :=
  Nat.nth Nat.Prime n
/-- Zero-based consecutive prime gap. Local copy of ErdosProblems.Erdos251.primeGap0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeGap0 (n : ℕ) : ℕ :=
  prime0 (n + 1) - prime0 n
/-- Local copy of ErdosProblems.Erdos251.PaperR7.signedWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def signedWindow (h N L : ℕ) : ℝ :=
  ∑ j ∈ Finset.range L,
    ((primeGap0 (N + h + j + 1) : ℝ) - primeGap0 (N + j + 1)) / 2 ^ (j + 1)
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
/-- States long251:xr:truncation from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.cofinal_escape_of_finite_truncation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cofinal_escape_of_finite_truncation (M : ℕ → ℝ)
    (hM : ∀ n, (primeGap0 n : ℝ) ≤ M n)
    (hsupply : ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N L : ℕ,
      N₀ ≤ N ∧ 1 ≤ L ∧ Summable (majorantRemainderTerm M h N L) ∧
      majorantRemainder M h N L < integerDistance (signedWindow h N L)) :
    CofinalNonintegralTailShifts realPrimeGapTail := by
  sorry
end PalomarCorpus.E251.PaperStatementsN

namespace PalomarCorpus.E251.PaperStatementsB
open Filter
open Topology
/-- States long251:res:complete-truncation from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperCompleteR20.finite_separation_complete in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_separation_complete (D : ℝ) (S R : ℕ → ℝ)
    (hR : ∀ L, 0 ≤ R L) (herr : ∀ L, |D-S L| ≤ R L)
    (hlim : Tendsto R atTop (𝓝 0)) :
    D ∉ Set.range ((↑) : ℤ → ℝ) ↔
      ∃ L, R L < Metric.infDist (S L) (Set.range ((↑) : ℤ → ℝ)) := by
  sorry
end PalomarCorpus.E251.PaperStatementsB

namespace PalomarCorpus.E251.PaperStatementsE
open Filter
open Topology
open scoped BigOperators
/-- The special indices of the printed bounded construction. Local copy of ErdosProblems.Erdos251.PaperR7.IsFactorialSpike, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsFactorialSpike (n : ℕ) : Prop := ∃ k : ℕ, 3 ≤ k ∧ n = k.factorial
/-- U_0=4; at factorials k! with k>=3 the carry is 6, otherwise it is 4. Local copy of ErdosProblems.Erdos251.PaperR7.factorialCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialCarry (n : ℕ) : ℤ := by
  classical
  exact if IsFactorialSpike n then 6 else 4
/-- a_0 is unused. At every positive index this is 2 U_(n-1) - U_n. Local copy of ErdosProblems.Erdos251.PaperR7.factorialCarryDigit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def factorialCarryDigit (n : ℕ) : ℤ :=
  if n = 0 then 0 else 2 * factorialCarry (n - 1) - factorialCarry n
/-- States long251:xr:boundedpolignac from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.bounded_recurring_values_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bounded_recurring_values_countermodel :
    (∀ n, 1 ≤ n → factorialCarryDigit n = 2 ∨
      factorialCarryDigit n = 4 ∨ factorialCarryDigit n = 8) ∧
    (∀ k, 3 ≤ k → factorialCarryDigit k.factorial = 2 ∧
      factorialCarryDigit (2 * k.factorial) = 4) ∧
    (∀ t, 0 < t → ∀ N, ∃ i j : ℕ, N ≤ i ∧ N ≤ j ∧ t ∣ i ∧ t ∣ j ∧
      factorialCarryDigit i = 2 ∧ factorialCarryDigit j = 4) ∧
    HasSum (fun j : ℕ => (factorialCarryDigit (j + 1) : ℝ) / 2 ^ (j + 1)) 4 ∧
    (∀ N, HasSum (fun j : ℕ =>
      (factorialCarryDigit (N + j + 1) : ℝ) / 2 ^ (j + 1)) (factorialCarry N : ℝ)) := by
  sorry
end PalomarCorpus.E251.PaperStatementsE
