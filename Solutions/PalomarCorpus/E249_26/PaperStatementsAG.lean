/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.TotientParityCoboundaryCountermodel
import Solutions.PalomarCorpus.E249_26.Statement

open Filter

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsAG

theorem exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs
    (N G K : ℕ) :
    ∃ k : ℕ,
      N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        parityCoboundaryWeight (2 ^ (k + i + 3)) = 6 ∧
        parityCoboundaryWeight (2 ^ (k + i + 3) + 1) = 0 := @Erdos249257.TotientParityCoboundaryCountermodel.exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs N G K

theorem exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel :
    ∃ c : ℕ → ℕ,
      (∀ N G K, ∃ k,
        N < 2 ^ (k + 3) ∧
        ∀ i : ℕ, i < K →
          2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
          c (2 ^ (k + i + 3)) = 6 ∧
          c (2 ^ (k + i + 3) + 1) = 0) ∧
      (∀ n, c n ≤ 6) ∧
      (∀ n, c n ≤ n) ∧
      (∀ n, c n % 2 = Nat.totient n % 2) ∧
      (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n) ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := @Erdos249257.TotientParityCoboundaryCountermodel.exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel

theorem parityCoboundaryWeight_le_self (n : ℕ) :
    parityCoboundaryWeight n ≤ n := @Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_self n

theorem parityCoboundaryWeight_le_six (n : ℕ) :
    parityCoboundaryWeight n ≤ 6 := @Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_six n

theorem parityCoboundaryWeight_mod_two_eq_totient (n : ℕ) :
    parityCoboundaryWeight n % 2 = Nat.totient n % 2 := @Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_mod_two_eq_totient n

theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2 := @Erdos249257.TotientParityCoboundaryCountermodel.tsum_parityCoboundaryWeight_eq_three_halves

end PalomarCorpus.E249.PaperStatementsAG
