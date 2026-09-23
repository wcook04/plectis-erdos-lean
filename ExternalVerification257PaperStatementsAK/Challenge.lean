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
`Erdos249257.BooleanMobiusExactTransition`, `Erdos249257.BooleanMobiusLocalRepair`,
`ErdosProblems.Erdos257.PaperCompleteR21.MersenneQuotientRowRecurrences`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStatementsAK

noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card

noncomputable def halfEndpointTarget (M : ℕ) : ℕ :=
  2 ^ (M - 1) - 1

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1

noncomputable def localEndpointDefect (D : Finset ℕ) (M : ℕ) : ℤ :=
  (halfEndpointTarget M : ℤ) - (localPrefixQuotient D M : ℤ)

noncomputable def localRepairInteger (D : Finset ℕ) (k n : ℕ) : ℤ :=
  2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
    (endpointDivisorContribution D n : ℤ)

/-- States record:257bm-i1a from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_floor_quotient_geometric_sum in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_floor_quotient_geometric_sum {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient M d = ∑ j ∈ Finset.Icc 1 (M / d), 2 ^ (M - j * d) := by
  sorry

/-- States record:257bm-i1a from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_next_floor_quotient {M d : ℕ} (hd : 2 ≤ d) :
    localMersenneQuotient (M + 1) d =
      2 * localMersenneQuotient M d + (if d ∣ M + 1 then 1 else 0) := by
  sorry

/-- States record:257bm-i1a from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_next_floor_quotient_no_fixed_point in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_next_floor_quotient_no_fixed_point {M d : ℕ} (hd : 2 ≤ d)
    (hfix : localMersenneQuotient (M + 1) d = localMersenneQuotient M d) :
    localMersenneQuotient M d = 0 ∧ localMersenneQuotient (M + 1) d = 0 := by
  sorry

/-- States record:257bm-i1a from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_next_quotient_sum in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_next_quotient_sum {D : Finset ℕ} {M : ℕ}
    (hD : ∀ d ∈ D, 2 ≤ d) :
    localPrefixQuotient D (M + 1) =
      2 * localPrefixQuotient D M + endpointDivisorContribution D (M + 1) := by
  sorry

/-- States record:257bm-i1c from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_repair_integer_eq_endpoint_defect in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_repair_integer_eq_endpoint_defect {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d)
    (hbelow : localPrefixQuotient D M ≤ halfEndpointTarget M) :
    localRepairInteger D 1 (M + 1) = localEndpointDefect D (M + 1) := by
  sorry

/-- States record:257bm-i1c from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_defect_succ in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_signed_endpoint_defect_succ {D : Finset ℕ} {M : ℕ}
    (hM : 1 ≤ M) (hD : ∀ d ∈ D, 2 ≤ d) :
    localEndpointDefect D (M + 1) =
      2 * localEndpointDefect D M + 1 -
        (endpointDivisorContribution D (M + 1) : ℤ) := by
  sorry

/-- States record:257bm-i1c from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_signed_endpoint_recurrence in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_signed_endpoint_recurrence (D : Finset ℕ) (k n : ℕ) :
    localRepairInteger D k n =
      2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
        (endpointDivisorContribution D n : ℤ) := by
  sorry

end Erdos249257.ExternalVerification257PaperStatementsAK
