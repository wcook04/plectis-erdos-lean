/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PrimeGapDyadicTail
import Solutions.PalomarCorpus.E251.Statement

namespace PalomarCorpus.E251.PrimeGapIdentity
export PalomarCorpus.E251.Shared (prime0 primeDyadicTerm primeGap0 primeGapDyadicTerm)

theorem prime0_le_polynomial (n : ℕ) :
    prime0 n ≤ 1250 * (n + 1) ^ 4 :=
  ErdosProblems.Erdos251.prime0_le_polynomial n

theorem primeSeries_summable : Summable primeDyadicTerm :=
  ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeGapSeries_summable : Summable primeGapDyadicTerm :=
  ErdosProblems.Erdos251.summable_primeGapDyadicTerm

theorem primeSeries_eq_two_add_primeGapSeries :
    (∑' n : ℕ, primeDyadicTerm n) =
      2 + ∑' n : ℕ, primeGapDyadicTerm n :=
  ErdosProblems.Erdos251.tsum_primeDyadicTerm_eq_two_add_primeGap_unconditional

theorem primeSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  ErdosProblems.Erdos251.irrational_tsum_primeDyadicTerm_iff_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeDisplayedSeries_eq_four_add_two_primeGapSeries :
    (∑' n : ℕ, primeDisplayedDyadicTerm n) =
      4 + 2 * ∑' n : ℕ, primeGapDyadicTerm n :=
  ErdosProblems.Erdos251.tsum_primeDisplayedDyadicTerm_eq_four_add_two_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

theorem primeDisplayedSeries_irrational_iff_primeGapSeries :
    Irrational (∑' n : ℕ, primeDisplayedDyadicTerm n) ↔
      Irrational (∑' n : ℕ, primeGapDyadicTerm n) :=
  ErdosProblems.Erdos251.irrational_tsum_primeDisplayedDyadicTerm_iff_primeGap
    ErdosProblems.Erdos251.summable_primeDyadicTerm

end PalomarCorpus.E251.PrimeGapIdentity
