/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #269

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos269.PaperCompleteR20.RealBaseShortInterval`,
`ErdosProblems.Erdos269.PaperCompleteR20.RealTwoPrimeKernel`,
`ErdosProblems.Erdos269.ResidueEscape`.
-/

namespace Erdos249257.ExternalVerification269PaperStatementsB

noncomputable def realTwoPrimeHeight (p q t : ℝ) : ℝ :=
  p ^ ⌊Real.logb p t⌋ * q ^ ⌊Real.logb q t⌋

noncomputable def realTwoPrimeKernel (p q : ℝ) (i j : ℕ) : ℝ :=
  (realTwoPrimeHeight p q (p ^ i * q ^ j))⁻¹

noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))

/-- States long269:res:short from the long record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_real_base_short_interval in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exponent_unique_real_base_short_interval
    {base lo hi weight : ℝ} {a b : ℕ}
    (hbase : 1 ≤ base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b := by
  sorry

/-- States long269:res:two-prime-rank from the long record for Erdős problem #269. Transported
from ErdosProblems.Erdos269.PaperCompleteR20.real_two_prime_separation in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem real_two_prime_separation {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    (∀ i j : ℕ, realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹) ∧
    (∀ i i' j j' : ℕ,
      realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
        realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0) := by
  sorry

/-- States long269:res:consumer from the long record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.no_bounded_positive_int_state_of_leastPositiveResidue in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem no_bounded_positive_int_state_of_leastPositiveResidue
    {C bound : ℕ} {x c : ℤ}
    (hC : 0 < C)
    (hcpos : 0 < c)
    (hcbound : Int.natAbs c ≤ bound)
    (hescape : bound < leastPositiveResidue C x)
    (hmod : Int.ModEq C c x) :
    False := by
  sorry

end Erdos249257.ExternalVerification269PaperStatementsB
