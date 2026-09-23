/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #68

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos68.FactorialChannelCertificate`,
`ErdosProblems.Erdos68.FactorialShiftFamilyOrbit`,
`ErdosProblems.Erdos68.PaperCompleteExisting`,
`ErdosProblems.Erdos68.PaperCompleteSupportedBands`,
`ErdosProblems.Erdos68.PrimeUnitTranslator`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification68PaperStatementsC

noncomputable def factorialGapTailTerm (D d : ℕ) : ℝ :=
  if D < d then
    (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)
  else 0

noncomputable def factorialGapTail (D : ℕ) : ℝ :=
  ∑' d : ℕ, factorialGapTailTerm D d

noncomputable def factorialGapSeries : ℝ :=
  factorialGapTail 1

noncomputable def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))

noncomputable def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)

noncomputable def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)

noncomputable def shiftCompanionTerm (t : ℤ) (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n.factorial : ℝ) * ((n.factorial : ℝ) + (t : ℝ))) else 0

noncomputable def shiftCompanionConstant (t : ℤ) : ℝ :=
  ∑' n : ℕ, shiftCompanionTerm t n

noncomputable def shiftGapTerm (t : ℤ) (n : ℕ) : ℝ :=
  if 2 ≤ n then 1 / ((n.factorial : ℝ) + (t : ℝ)) else 0

noncomputable def shiftGapSeries (t : ℤ) : ℝ :=
  ∑' n : ℕ, shiftGapTerm t n

/-- States long68:res:bandbreakpoint, res:bandbreakpoint from the long record and the short
record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.supported_breakpoint_escape in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supported_breakpoint_escape (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hz : channelNumerator f d = 0) (hm : factorialMoment f ≠ 0) :
    ∃ n ∈ f.support, 2 * d ≤ n := by
  sorry

/-- States long68:res:bandbreakpoint, res:bandbreakpoint from the long record and the short
record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.supported_first_band_cancellation in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supported_first_band_cancellation (f : ℕ →₀ ℤ) (d : ℕ)
    (hlo : ∀ n ∈ f.support, d ≤ n)
    (hhi : ∀ n ∈ f.support, n < 2 * d)
    (hz : channelNumerator f d = 0) : factorialMoment f = 0 := by
  sorry

/-- States long68:res:normalform from the long record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.supported_integral_normal_form in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supported_integral_normal_form (f : ℕ →₀ ℤ) {d : ℕ} (hd : 2 ≤ d) :
    ∃ k : ℤ, channelNumerator f d = factorialMoment f + ((d.factorial : ℤ) - 1) * k := by
  sorry

/-- States long68:res:bandbreakpoint, res:bandbreakpoint from the long record and the short
record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.supported_quotient_band in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem supported_quotient_band (f : ℕ →₀ ℤ) (d k : ℕ)
    (hlo : ∀ n ∈ f.support, k * d ≤ n)
    (hhi : ∀ n ∈ f.support, n < (k + 1) * d) :
    factorialMoment f = (d.factorial : ℤ) ^ k * channelNumerator f d := by
  sorry

/-- States long68:res:shift-family from the long record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.uniform_family_boundary in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem uniform_family_boundary {t : ℤ} (ht : -1 ≤ t) :
    (¬ Irrational (shiftGapSeries t) ↔
      ∃ M : ℕ, ∀ m : ℕ, M ≤ m →
        (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2) ∧
    (Irrational (shiftGapSeries t) ↔
      ∀ B : ℕ, ∃ m : ℕ, B < m ∧
        ¬ (m : ℤ) ∣ ⌈(t : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant t⌉ - 2) := by
  sorry

/-- States long68:res:shift-family from the long record for Erdős problem #68. Transported from
ErdosProblems.Erdos68.PaperComplete.uniform_family_members in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem uniform_family_members :
    shiftGapSeries (-1) = factorialGapSeries ∧
    shiftGapSeries 0 = Real.exp 1 - 2 ∧
    (∀ m : ℕ, ⌈(0 : ℝ) * (m.factorial : ℝ) * shiftCompanionConstant 0⌉ = 0) ∧
    (∀ m : ℕ, 3 ≤ m → ¬ (m : ℤ) ∣ (0 : ℤ) - 2) ∧
    Irrational (Real.exp 1) := by
  sorry

end Erdos249257.ExternalVerification68PaperStatementsC
