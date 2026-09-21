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
`ErdosProblems.Erdos269.PaperCompleteR21.TwoPrimeSums`,
`ErdosProblems.Erdos269.PaperR7AnalyticInterfaces`.
-/

open Polynomial
open scoped BigOperators

namespace Erdos249257.ExternalVerification269PaperStatementsY

noncomputable def heckeMahlerSeries (θ β α : ℝ) : ℝ :=
  ∑' n : ℕ, ∑ k ∈ Finset.Icc 1 ⌊(n : ℝ) * θ⌋₊, β ^ n * α ^ k

noncomputable def BugeaudLaurentTranscendence : Prop :=
  ∀ θ β α : ℝ, Irrational θ → 0 < θ → θ < 1 →
    IsAlgebraic ℚ β → IsAlgebraic ℚ α → β ≠ 0 → α ≠ 0 →
    |β| < 1 → |β| * |α| ^ θ < 1 →
    Transcendental ℚ (heckeMahlerSeries θ β α)

noncomputable def twoPrimeHeckeValue (p q : ℕ) : ℝ :=
  ∑' n : ℕ, ((p : ℝ)⁻¹) ^ n *
    ((q : ℝ)⁻¹) ^ ⌊(n : ℝ) * Real.logb q p⌋₊

/-- States long269:res:lead-two-prime, res:two-prime-transcendence from the long record and the
short record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR21.transcendental_heckeValue in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem transcendental_heckeValue (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (twoPrimeHeckeValue p q) := by
  sorry

end Erdos249257.ExternalVerification269PaperStatementsY
