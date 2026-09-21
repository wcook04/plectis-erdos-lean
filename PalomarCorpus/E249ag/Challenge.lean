/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band g

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open Filter

namespace PalomarCorpus.E249.PaperStatementsAG
open Filter
/-- Lacunary spike ranks `2^(k+3)`, beginning at `8`. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.IsLargePowerTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsLargePowerTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 ^ (k + 3)
/-- The zero-one indicator of the lacunary spike ranks. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.largePowerTwoBit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def largePowerTwoBit (n : ℕ) : ℕ := by
  classical
  exact if IsLargePowerTwo n then 1 else 0
/-- Rational base coefficients before adding zero-valued sparse carries. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.parityBaseWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def parityBaseWeight : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 4
/-- The parity countermodel. Natural subtraction is exact because every negative spike lands on a base coefficient `4`. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def parityCoboundaryWeight (n : ℕ) : ℕ :=
  parityBaseWeight n + 2 * largePowerTwoBit n -
    4 * largePowerTwoBit (n - 1)
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from Erdos249257.TotientParityCoboundaryCountermodel.exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs
    (N G K : ℕ) :
    ∃ k : ℕ,
      N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        parityCoboundaryWeight (2 ^ (k + i + 3)) = 6 ∧
        parityCoboundaryWeight (2 ^ (k + i + 3) + 1) = 0 := by
  sorry
/-- States prop:parity from the long record for Erdős problem #249. Transported from Erdos249257.TotientParityCoboundaryCountermodel.exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_self in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem parityCoboundaryWeight_le_self (n : ℕ) :
    parityCoboundaryWeight n ≤ n := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_six in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem parityCoboundaryWeight_le_six (n : ℕ) :
    parityCoboundaryWeight n ≤ 6 := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_mod_two_eq_totient in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem parityCoboundaryWeight_mod_two_eq_totient (n : ℕ) :
    parityCoboundaryWeight n % 2 = Nat.totient n % 2 := by
  sorry
/-- States prop:parity from the long record for Erdős problem #249. Transported from Erdos249257.TotientParityCoboundaryCountermodel.tsum_parityCoboundaryWeight_eq_three_halves in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAG
