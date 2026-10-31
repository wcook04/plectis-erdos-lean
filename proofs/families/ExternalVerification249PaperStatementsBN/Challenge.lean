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
`Erdos249257.MersenneLambertLadder`,
`ErdosProblems.Erdos249.PaperCompleteR21.CompositeDilationIdentity`.
-/

open ArithmeticFunction

namespace Erdos249257.ExternalVerification249PaperStatementsBN

noncomputable def totientZ : ArithmeticFunction ℤ :=
  ⟨fun n => (Nat.totient n : ℤ), by simp⟩

noncomputable def primWeight : ArithmeticFunction ℤ := totientZ * moebius

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_mul_zeta in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totient_convolution_weight_mul_zeta (n : ℕ) :
    ∑ e ∈ n.divisors, primWeight e = (Nat.totient n : ℤ) := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_not_periodic in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totient_convolution_weight_not_periodic :
    ¬ ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ, primWeight (n + p) =
        primWeight n := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_prime in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_convolution_weight_prime {p : ℕ} (hp : p.Prime) :
    primWeight p = (p : ℤ) - 2 := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_unbounded in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totient_convolution_weight_unbounded :
    ¬ ∃ B : ℕ, ∀ n : ℕ, primWeight n ≤ (B : ℤ) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsBN
