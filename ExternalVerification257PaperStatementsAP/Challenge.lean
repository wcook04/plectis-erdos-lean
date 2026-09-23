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
`Erdos249257.CyclicTensorMobiusShadow`, `Erdos249257.MersenneShadowCyclotomicNoncollapse`,
`Erdos249257.MersenneShadowDenominatorGrowth`, `Erdos249257.RadicalMobiusShadow`.
-/

open scoped BigOperators
open scoped Polynomial

namespace Erdos249257.ExternalVerification257PaperStatementsAP

noncomputable def oddJordanScalar (r : ℕ) : ℤ :=
  ∏ q ∈ r.primeFactors.filter (fun q => q ≠ 2), ((q : ℤ) ^ 2 - 1)

noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)

noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

noncomputable def lcmRadical (t : ℕ) : ℕ :=
  squarefreeKernel (lcmHeight t)

noncomputable def lcmScale (t : ℕ) : ℕ :=
  lcmHeight t / lcmRadical t

noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)

noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)

noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)

/-- States thm:mersenne-channel-growth from the long record for Erdős problem #257. Transported
from Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_scaledMobiusShadow_den_exact in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem lcmHeight_scaledMobiusShadow_den_exact (t : ℕ) :
    ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den =
      mersenne (lcmRadical t) /
        Nat.gcd (mersenne (lcmRadical t))
          (lcmScale t *
            (oddJordanScalar (lcmRadical t)).natAbs) := by
  sorry

end Erdos249257.ExternalVerification257PaperStatementsAP
