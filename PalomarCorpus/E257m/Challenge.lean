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

open ArithmeticFunction
open Filter
open Set
open scoped ArithmeticFunction.Moebius
open scoped ENNReal
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStatementsM
open ArithmeticFunction
open Filter
open Set
open scoped ArithmeticFunction.Moebius
open scoped ENNReal
open MeasureTheory
open Topology
/-- Integer numerator of the same dyadic prefix at denominator `2^N`. Local copy of Erdos249257.binaryCoeffPrefixNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffPrefixNumerator (c : ℕ → ℕ) : ℕ → ℕ
  | 0 => 0
  | N + 1 => 2 * binaryCoeffPrefixNumerator c N + c (N + 1)
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
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- Local copy of ErdosProblems.Erdos257.PaperCompleteR20.paperIntegerDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperIntegerDefect (x : ℝ) (N : ℕ) : ℤ :=
  ⌊(2 : ℝ)^N*x⌋ - binaryCoeffPrefixNumerator (supportCoeff (greedyMersenneSupport x)) N
/-- States res:general-repair from the short record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.paper_general_repair_criteria in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_general_repair_criteria {x : ℝ} (hx : 0 ≤ x) :
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N) ∧
    (x ∈ mersenneAchievementSet ↔ ∀ K : ℕ, ∃ N, K ≤ N ∧
      N < K+2*Nat.sqrt K+12 ∧ paperIntegerDefect x (N+1) ≤ paperIntegerDefect x N) := by
  sorry
end PalomarCorpus.E257.PaperStatementsM
