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
`ErdosProblems.Erdos269.PaperCompleteR21.TwoPrimeSums`.
-/

open Polynomial
open scoped BigOperators

namespace Erdos249257.ExternalVerification269PaperStatementsX

noncomputable def heckeMahlerSeries (θ β α : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ) * θ⌋₊, β ^ n * α ^ k

noncomputable def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)

noncomputable def SmoothSet (p q : ℕ) : Set ℕ := {n : ℕ | 0 < n ∧ ∃ i j : ℕ, n = p ^ i * q ^ j}

noncomputable def smoothPrefixPairs (p q x : ℕ) : Finset (ℕ × ℕ) :=
  (((Finset.range (Nat.log p x + 1)) ×ˢ (Finset.range (Nat.log q x + 1))).filter
    fun e => p ^ e.1 * q ^ e.2 ≤ x)

noncomputable def runningLcm (p q x : ℕ) : ℕ :=
  (smoothPrefixPairs p q x).lcm fun e => p ^ e.1 * q ^ e.2

noncomputable def runningLcmValues (p q : ℕ) : Set ℕ := (runningLcm p q) '' SmoothSet p q

noncomputable def distinctSum (p q : ℕ) : ℝ :=
  ∑' H : runningLcmValues p q, (((H : ℕ) : ℝ))⁻¹

noncomputable def repeatedSum (p q : ℕ) : ℝ :=
  ∑' n : SmoothSet p q, ((runningLcm p q (n : ℕ) : ℝ))⁻¹

/-- States long269:res:lead-two-prime, res:two-prime-transcendence from the long record and the
short record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR21.two_prime_sums_transcendental in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_prime_sums_transcendental (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (distinctSum p q) ∧ Transcendental ℚ (repeatedSum p q) := by
  sorry

/-- States long269:res:lead-two-prime from the long record for Erdős problem #269. Transported
from ErdosProblems.Erdos269.PaperCompleteR21.two_prime_transcendence in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_prime_transcendence (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Transcendental ℚ (repeatedSum p q) ∧ Transcendental ℚ (distinctSum p q) := by
  sorry

end Erdos249257.ExternalVerification269PaperStatementsX
