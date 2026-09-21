/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #269, band b

Erdős problem #269 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E269` under the Challenge size ceiling; it does not replace it.
-/

namespace PalomarCorpus.E269.PaperStatementsB
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.realTwoPrimeHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTwoPrimeHeight (p q t : ℝ) : ℝ :=
  p ^ ⌊Real.logb p t⌋ * q ^ ⌊Real.logb q t⌋
/-- Local copy of ErdosProblems.Erdos269.PaperCompleteR20.realTwoPrimeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realTwoPrimeKernel (p q : ℝ) (i j : ℕ) : ℝ :=
  (realTwoPrimeHeight p q (p ^ i * q ^ j))⁻¹
/-- Canonical positive representative of an integer modulo `C`: a zero residue is represented by `C`, and every nonzero residue by its nonnegative Euclidean remainder. The definition is total at `C = 0`, but all theorems using its positive-representative meaning assume `0 < C`. Local copy of ErdosProblems.Erdos269.leastPositiveResidue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))
/-- States long269:res:short from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_real_base_short_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exponent_unique_real_base_short_interval
    {base lo hi weight : ℝ} {a b : ℕ}
    (hbase : 1 ≤ base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b := by
  sorry
/-- States long269:res:two-prime-rank from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperCompleteR20.real_two_prime_separation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_two_prime_separation {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    (∀ i j : ℕ, realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹) ∧
    (∀ i i' j j' : ℕ,
      realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
        realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0) := by
  sorry
/-- States long269:res:consumer from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.no_bounded_positive_int_state_of_leastPositiveResidue in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_bounded_positive_int_state_of_leastPositiveResidue
    {C bound : ℕ} {x c : ℤ}
    (hC : 0 < C)
    (hcpos : 0 < c)
    (hcbound : Int.natAbs c ≤ bound)
    (hescape : bound < leastPositiveResidue C x)
    (hmod : Int.ModEq C c x) :
    False := by
  sorry
end PalomarCorpus.E269.PaperStatementsB
