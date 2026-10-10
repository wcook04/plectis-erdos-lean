/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.DyadicPrefixCompression`.
-/

open Set

namespace Erdos249257.ExternalVerification257PaperStructuresCL

noncomputable def dyadicResidualIntNumerator (p r : ℤ) (c D : ℕ) : ℤ :=
  p * (D : ℤ) - ((2 ^ c : ℕ) : ℤ) * r

noncomputable def dyadicResidualIntRat (p r : ℤ) (c D : ℕ) : ℚ :=
  Rat.divInt (dyadicResidualIntNumerator p r c D) (((2 ^ c * D : ℕ) : ℤ))

/-- States lem:denominator-sandwich from the long record for Erdős problem #257. Transported
from Erdos249257.dyadicResidualIntNumerator_coprime_oddDenominator in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicResidualIntNumerator_coprime_oddDenominator
    (p r : ℤ) (c D : ℕ) (hDodd : Odd D)
    (hrD : r.natAbs.Coprime D) :
    (dyadicResidualIntNumerator p r c D).natAbs.Coprime D := by
  sorry

/-- States lem:denominator-sandwich from the long record for Erdős problem #257. Transported
from Erdos249257.dyadicResidualInt_denominator_sandwich in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicResidualInt_denominator_sandwich
    (p r : ℤ) (c D : ℕ) (hDpos : 0 < D)
    (hND : (dyadicResidualIntNumerator p r c D).natAbs.Coprime D) :
    D ∣ (dyadicResidualIntRat p r c D).den ∧
      (dyadicResidualIntRat p r c D).den ∣ 2 ^ c * D := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresCL
