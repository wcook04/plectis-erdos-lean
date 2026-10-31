/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PrimitiveQuinticInteriorTail`.
-/

namespace Erdos249257.ExternalVerification1041PaperStatementsM

/-- States prop:primitive-quintic-two-tail-energy-selector from the long record for Erdős
problem #1041. Transported from
ErdosProblems.Erdos1041.primitiveInterior_exists_two_tailEnergy_lt_one in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem primitiveInterior_exists_two_tailEnergy_lt_one
    {r : ℝ}
    {x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : ℝ}
    (hr : 0 < r) (hr2 : r < 2)
    (hs0 : 0 ≤ s0) (hs0one : s0 ≤ 1) (hx0s : x0 ^ 2 ≤ s0)
    (hs1 : 0 ≤ s1) (hs1one : s1 ≤ 1) (hx1s : x1 ^ 2 ≤ s1)
    (hs2 : 0 ≤ s2) (hs2one : s2 ≤ 1) (hx2s : x2 ^ 2 ≤ s2)
    (hs3 : 0 ≤ s3) (hs3one : s3 ≤ 1) (hx3s : x3 ^ 2 ≤ s3)
    (hs4 : 0 ≤ s4) (hs4one : s4 ≤ 1) (hx4s : x4 ^ 2 ≤ s4)
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : (2 * x0 ^ 2 - s0) + (2 * x1 ^ 2 - s1) +
        (2 * x2 ^ 2 - s2) + (2 * x3 ^ 2 - s3) +
        (2 * x4 ^ 2 - s4) = r ^ 2)
    (hm3 : (4 * x0 ^ 3 - 3 * s0 * x0) +
        (4 * x1 ^ 3 - 3 * s1 * x1) +
        (4 * x2 ^ 3 - 3 * s2 * x2) +
        (4 * x3 ^ 3 - 3 * s3 * x3) +
        (4 * x4 ^ 3 - 3 * s4 * x4) = -r ^ 3) :
    (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsM
