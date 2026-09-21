/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band c

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology

namespace PalomarCorpus.E257.PaperStatementsBC
open Filter
open Topology
/-- **The Erdős #257 support series** `∑_{a ∈ A} 1/(b^a - 1)`, as an indicator series over ℕ. The `a = 0` term is `1/(1-1) = 0` under real division-by-zero conventions, so supports containing `0` contribute nothing spurious. Local copy of Erdos249257.erdosSupportSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}` — the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- The paper's terminal carry, with its sum reindexed from `j = 2, ..., M` to `j = 0, ..., M - 2`. Local copy of ErdosProblems.Erdos257.PaperCompleteR20.terminalPaperCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def terminalPaperCarry (A : Set ℕ) (M : ℕ) : ℤ :=
  (2 : ℤ) ^ (M - 1) -
    ∑ j ∈ Finset.range (M - 1),
      (2 : ℤ) ^ (M - 2 - j) * (supportCoeff A (j + 2) : ℤ)
/-- The full prime-power part determined by a finite set of primes. Local copy of ErdosProblems.Erdos257.PaperCompleteR7.primeSetPart, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeSetPart (P : Finset ℕ) (a : ℕ) : ℕ :=
  ∏ p ∈ P, p ^ a.factorization p
/-- The literal weighted term at an integer base. Local copy of ErdosProblems.Erdos257.PaperCompleteR7.primeWeightedTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeWeightedTerm (b : ℕ) (P : Finset ℕ) (a : ℕ) : ℝ :=
  (primeSetPart P a : ℝ) /
    ((a : ℝ) * ((b : ℝ) ^ primeSetPart P a - 1))
/-- The weighted hypothesis, not its irrationality conclusion. Local copy of ErdosProblems.Erdos257.PaperCompleteR7.FinitePrimeWeighted, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FinitePrimeWeighted (b : ℕ) (A : Set ℕ) : Prop :=
  ∃ P : Finset ℕ, P.Nonempty ∧ (∀ p ∈ P, Nat.Prime p) ∧
    Summable (Set.indicator A (primeWeightedTerm b P))
/-- States res:terminalhalf from the short record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.paper_terminalhalf in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_terminalhalf
    (M : ℕ → ℕ) (A : ℕ → Set ℕ)
    (hM : ∀ j, 1 ≤ M j)
    (hlim : Filter.Tendsto M Filter.atTop Filter.atTop)
    (hA : ∀ j n, n ∈ A j → 2 ≤ n ∧ n ≤ M j)
    (herr : Filter.Tendsto
      (fun j ↦ |(terminalPaperCarry (A j) (M j) : ℝ)| / (2 : ℝ) ^ M j)
      Filter.atTop (nhds 0)) :
    ∃ B : Set ℕ, 0 ∉ B ∧ B.Infinite ∧
      erdosSupportSeries 2 B = (1 : ℝ) / 2 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.irrational_residueClass_positive_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_residueClass_positive_support
    (b m : ℕ) (c : ℤ) (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Irrational (erdosSupportSeries b
      {n : ℕ | 0 < n ∧ (n : ℤ) % (m : ℤ) = c % (m : ℤ)}) := by
  sorry
/-- States eq:weighted-fixed-base, eq:weighted-return, res:weighted-support from the short record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR8.finitePrimeWeighted_fixedBase_hereditary in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finitePrimeWeighted_fixedBase_hereditary
    (b : ℕ) (H : Set ℕ) (hb : 2 ≤ b) (hH0 : 0 ∉ H)
    (hH : FinitePrimeWeighted b H) :
    ∀ A : Set ℕ, A ⊆ H → A.Infinite →
      Irrational (erdosSupportSeries b A) := by
  sorry
end PalomarCorpus.E257.PaperStatementsBC
