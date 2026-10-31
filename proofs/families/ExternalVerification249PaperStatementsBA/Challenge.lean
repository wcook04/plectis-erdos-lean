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
`Erdos249257.MersenneLambertLadder`, `Erdos249257.TotientShiftedMobiusPulse`,
`ErdosProblems.Erdos249.PaperCompleteR21.LambertDivisorTransform`,
`ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion`.
-/

open scoped BigOperators
open ArithmeticFunction

namespace Erdos249257.ExternalVerification249PaperStatementsBA

noncomputable def forwardMultipleQuotient (N d : ℕ) : ℕ := N / d + 1

noncomputable def forwardMultipleShift (N d : ℕ) : ℕ := d - N % d

noncomputable def lambertValue (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, f (n : ℕ) / ((2 : ℝ) ^ (n : ℕ) - 1)

noncomputable def totientZ : ArithmeticFunction ℤ :=
  ⟨fun n => (Nat.totient n : ℤ), by simp⟩

noncomputable def primWeight : ArithmeticFunction ℤ := totientZ * moebius

/-- States catalogue:cert:d7 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.alpha_divisor_sum_eq_totient in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem alpha_divisor_sum_eq_totient (n : ℕ) :
    ∑ e ∈ n.divisors, ((primWeight e : ℤ) : ℝ) = (Nat.totient n : ℝ) := by
  sorry

/-- States prop:MP-01-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.forwardMultipleShift_least in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem forwardMultipleShift_least (N : ℕ) {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hlt : m < forwardMultipleShift N d) : ¬ d ∣ N + m := by
  sorry

/-- States prop:MP-01-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_enumeration in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem forwardMultiple_enumeration (N : ℕ) {d : ℕ} (hd : 0 < d) (l : ℕ) :
    N + (forwardMultipleShift N d + d * l) =
      d * (forwardMultipleQuotient N d + l) := by
  sorry

/-- States prop:MP-01-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_spec in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem forwardMultiple_spec (N : ℕ) {d : ℕ} (hd : 0 < d) :
    forwardMultipleShift N d = d - N % d ∧
      forwardMultipleQuotient N d = N / d + 1 ∧
      1 ≤ forwardMultipleShift N d ∧
      forwardMultipleShift N d ≤ d ∧
      d ∣ N + forwardMultipleShift N d := by
  sorry

/-- States catalogue:cert:d7 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_alpha_eq_totientSeries in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem lambertValue_alpha_eq_totientSeries :
    lambertValue (fun d => ((primWeight d : ℤ) : ℝ))
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsBA
