/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR21.ExactOrbitRecordDichotomy`,
`ErdosProblems.Erdos243.ReciprocalTailRigidity`.
-/

open Filter

namespace Erdos249257.ExternalVerification243PaperStructuresAA

noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

/-- States long243:res:slownegative from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.tail_multiplier_quadratic_lower in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tail_multiplier_quadratic_lower (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (n : ℕ) (hsmall : 4 * Int.natAbs (E n) < C n) :
    4 * a n ^ 2 ≤ 5 * a (n + 1) + 5 * a n := by
  sorry

end Erdos249257.ExternalVerification243PaperStructuresAA
