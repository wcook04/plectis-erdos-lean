/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusLocalRepair`, `Erdos249257.CertificateKernel`,
`Erdos249257.HalfCylinderIntegerGreedy`,
`ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences`,
`ErdosProblems.Erdos257.PaperCompleteR21.OddReciprocalDenominators`.
-/

open scoped BigOperators
open Filter
open Topology

namespace Erdos249257.ExternalVerification257PaperStatementsAN

noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def finiteErdosSum (F : Finset Nat) (b : Nat) : Rat :=
  ∑ n ∈ F, 1 / ((b : Rat) ^ n - 1)

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

/-- States lem:half-divisor-unit-drop from the long record for Erdős problem #257. Transported
from Erdos249257.HalfCylinderIntegerGreedy.supportCoeff_insert_eq_add_indicator in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem supportCoeff_insert_eq_add_indicator
    (A : Set ℕ) {d n : ℕ} (hdA : d ∉ A) :
    supportCoeff (insert d A) n =
      supportCoeff A n + if d ∈ n.divisors then 1 else 0 := by
  sorry

/-- States record:257bm-i1c from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_endpoint_term_counts_divisors in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_endpoint_term_counts_divisors {D : Finset ℕ} {n : ℕ}
    (hn : 0 < n) :
    endpointDivisorContribution D n = (D.filter fun d ↦ d ∣ n).card ∧
      endpointDivisorContribution D n = supportCoeff (↑D : Set ℕ) n := by
  sorry

/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_finiteErdosSum_den_odd in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_finiteErdosSum_den_odd (F : Finset ℕ) (h0 : 0 ∉ F) :
    Odd (finiteErdosSum F 2).den := by
  sorry

/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_finite_support_series_ne_half in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_finite_support_series_ne_half
    (A : Set ℕ) (hfinite : A.Finite) (hzero : 0 ∉ A) :
    erdosSupportSeries 2 A ≠ (1 : ℝ) / 2 := by
  sorry

/-- States record:257bm-i10 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_half_representing_support_is_infinite in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_half_representing_support_is_infinite
    (A : Set ℕ) (hzero : 0 ∉ A)
    (hvalue : erdosSupportSeries 2 A = (1 : ℝ) / 2) :
    A.Infinite := by
  sorry

end Erdos249257.ExternalVerification257PaperStatementsAN
