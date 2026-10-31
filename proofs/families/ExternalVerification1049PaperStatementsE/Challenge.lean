/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.AllRow.Filtered`, `ErdosProblems.Erdos1049.AllRow.FiniteStates`,
`ErdosProblems.Erdos1049.PaperCompleteR21.AllRowInitialCoefficient`,
`ErdosProblems.Erdos1049.RationalBaseLambert`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification1049PaperStatementsE

noncomputable abbrev S := PowerSeries ℤ

noncomputable def Agree (D : ℕ) (f g : S) : Prop :=
  ∀ d, d < D → PowerSeries.coeff d f = PowerSeries.coeff d g

noncomputable def finiteRatio (a : ℕ → S) (K n : ℕ) : S :=
  1 + ∑ s ∈ Finset.range K,
    a (s + 1) * PowerSeries.X ^ ((n + 1) * (s + 1))

noncomputable def rowExponent (j l : ℕ) : ℕ := j * (j + 1) / 2 + j * l

noncomputable def CoordinatewiseCorridor
    (a b N K Q digit : ℕ) : Prop :=
  0 < a ∧ 0 < Q ∧ 0 < digit ∧ digit ≤ N + K ∧
    a ^ K ∣ Q * digit ∧
    Q * b ^ (N + K + 1) < a ^ (K + 1)

noncomputable def paperRatio (a : ℕ → S) (n : ℕ) : S :=
  PowerSeries.mk fun d => PowerSeries.coeff d (finiteRatio a (d + 1) n)

noncomputable def paperReducedSeries (a : ℕ → S) : PowerSeries ℤ :=
  PowerSeries.mk fun s => if s = 0 then 1 else PowerSeries.constantCoeff (a s)

noncomputable def paperReciprocal (a : ℕ → S) (r : ℕ) : ℤ :=
  PowerSeries.coeff r (PowerSeries.invOfUnit (paperReducedSeries a) 1)

/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported
from ErdosProblems.Erdos1049.PaperCompleteR21.paperE_eq_rowExponent in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperE_eq_rowExponent (m j : ℕ) (hjm : j ≤ m) :
    m * j - j * (j - 1) / 2 = rowExponent j (m - j) := by
  sorry

/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported
from ErdosProblems.Erdos1049.PaperCompleteR21.paperRatio_agree in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperRatio_agree (a : ℕ → S) (n D K : ℕ) (hDK : D ≤ K) :
    Agree D (paperRatio a n) (finiteRatio a K n) := by
  sorry

/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported
from ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_rec in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperReciprocal_rec (a : ℕ → S) (i : ℕ) :
    paperReciprocal a (i + 1) =
      -(∑ s ∈ Finset.range (i + 1),
          PowerSeries.constantCoeff (a (s + 1)) * paperReciprocal a (i - s)) := by
  sorry

/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported
from ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal_zero in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperReciprocal_zero (a : ℕ → S) : paperReciprocal a 0 = 1 := by
  sorry

/-- States long1049:res:corridorbound from the long record for Erdős problem #1049. Transported
from ErdosProblems.Erdos1049.coordinatewiseCorridor_implies_pow_lt_linear in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coordinatewiseCorridor_implies_pow_lt_linear
    {a b N K Q digit : ℕ}
    (h : CoordinatewiseCorridor a b N K Q digit) :
    b ^ (N + K + 1) < a * (N + K) := by
  sorry

/-- States long1049:res:sevenhalves, res:sevenhalves from the long record and the short record
for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.sevenHalves_archimedean_height_condition in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sevenHalves_archimedean_height_condition :
    Real.log 7 / Real.log ((7 : ℝ) / 2) <
      ((1 : ℝ) / 2 + 1 / Real.pi ^ 2)⁻¹ := by
  sorry

/-- States long1049:res:exp from the long record for Erdős problem #1049. Transported from
ErdosProblems.Erdos1049.three_mul_lt_two_pow_succ in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem three_mul_lt_two_pow_succ {x : ℕ} (hx : 2 ≤ x) :
    3 * x < 2 ^ (x + 1) := by
  sorry

end Erdos249257.ExternalVerification1049PaperStatementsE
