/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #251, band o

Erdős problem #251 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E251` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology
open scoped BigOperators

namespace PalomarCorpus.E251.PaperStatementsO
open Filter
open Topology
open scoped BigOperators
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
/-- A real number is integral when it is the cast of an integer. Local copy of ErdosProblems.Erdos251.RealIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def RealIntegral (x : ℝ) : Prop :=
  ∃ z : ℤ, x = z
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
/-- Difference between two real tail states separated by `h` steps. Local copy of ErdosProblems.Erdos251.realTailShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTailShift (T : ℕ → ℝ) (h N : ℕ) : ℝ :=
  T (N + h) - T N
/-- States long251:res:explicit-remainder from the long record for Erdős problem #251. Transported from ErdosProblems.Erdos251.PaperR7.explicit_remainder_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem explicit_remainder_certificate (h N L : ℕ) :
    |realTailShift realPrimeGapTail h N - signedWindow h N L| ≤ explicitRemainder h N L ∧
    (|signedWindow h N L| + explicitRemainder h N L < 1 →
      |realTailShift realPrimeGapTail h N| < 1) ∧
    (explicitRemainder h N L < integerDistance (signedWindow h N L) →
      ¬ RealIntegral (realTailShift realPrimeGapTail h N)) := by
  sorry
end PalomarCorpus.E251.PaperStatementsO
