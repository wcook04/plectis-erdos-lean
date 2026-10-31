/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.TotientParityCoboundaryCountermodel`.
-/

open Filter

namespace Erdos249257.ExternalVerification249PaperStatementsAG

noncomputable def IsLargePowerTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 ^ (k + 3)

noncomputable def largePowerTwoBit (n : ℕ) : ℕ := by
  classical
  exact if IsLargePowerTwo n then 1 else 0

noncomputable def parityBaseWeight : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 4

noncomputable def parityCoboundaryWeight (n : ℕ) : ℕ :=
  parityBaseWeight n + 2 * largePowerTwoBit n -
    4 * largePowerTwoBit (n - 1)

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
Erdos249257.TotientParityCoboundaryCountermodel.exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem exists_later_arbitrarily_many_separated_parityCoboundaryWeight_carry_pairs
    (N G K : ℕ) :
    ∃ k : ℕ,
      N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        parityCoboundaryWeight (2 ^ (k + i + 3)) = 6 ∧
        parityCoboundaryWeight (2 ^ (k + i + 3) + 1) = 0 := by
  sorry

/-- States prop:parity from the long record for Erdős problem #249. Transported from
Erdos249257.TotientParityCoboundaryCountermodel.exists_totientParity_arbitrarilyManySeparatedCarry_rational_countermodel
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
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

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_self in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem parityCoboundaryWeight_le_self (n : ℕ) :
    parityCoboundaryWeight n ≤ n := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_le_six in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem parityCoboundaryWeight_le_six (n : ℕ) :
    parityCoboundaryWeight n ≤ 6 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight_mod_two_eq_totient in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem parityCoboundaryWeight_mod_two_eq_totient (n : ℕ) :
    parityCoboundaryWeight n % 2 = Nat.totient n % 2 := by
  sorry

/-- States prop:parity from the long record for Erdős problem #249. Transported from
Erdos249257.TotientParityCoboundaryCountermodel.tsum_parityCoboundaryWeight_eq_three_halves
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2 := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsAG
