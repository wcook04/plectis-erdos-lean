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
`ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser`,
`ErdosProblems.Erdos243.PaperCompleteR21.ClassicalHalfspaceSigns`,
`ErdosProblems.Erdos243.PaperCompleteR21.SlowGrowthProductIncrements`,
`ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState`,
`ErdosProblems.Erdos243.PaperCompleteR7.Frontier`,
`ErdosProblems.Erdos243.PaperCompleteR7.ProductDefect`,
`ErdosProblems.Erdos243.PaperCompleteR7.QuantitativeTail`,
`ErdosProblems.Erdos243.ReciprocalTailRigidity`.
-/

open Filter
open scoped BigOperators

namespace Erdos249257.ExternalVerification243PaperStatementsL

noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2

noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n

noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

noncomputable def canonicalError (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℤ :=
  centeredState (a n : ℤ) ((canonicalDenominator a q n : ℕ) : ℤ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℤ)

noncomputable def shiftedCorrectionTerm (a aNext C CNext E ENext : ℝ) : ℝ :=
  (1 - E / C) * (a - 1 + ENext / CNext) / aNext

noncomputable def canonicalCorrection (a : ℕ → ℕ) (p : ℤ) (q : ℕ) (n : ℕ) : ℝ :=
  shiftedCorrectionTerm (a n : ℝ) (a (n + 1) : ℝ)
    ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)
    ((canonicalNaturalNumerator a p q (n + 1) : ℕ) : ℝ)
    ((canonicalError a p q n : ℤ) : ℝ) ((canonicalError a p q (n + 1) : ℤ) : ℝ)

noncomputable def productDefect (a : ℕ → ℕ) (n : ℕ) : ℝ :=
  (prefixProduct a n : ℝ) / (a n : ℝ) *
    ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1)

noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős
problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.canonicalCorrection_pos_and_lt_three_div in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem canonicalCorrection_pos_and_lt_three_div
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    ∃ N, ∀ n, N ≤ n →
      0 < canonicalCorrection a p q n ∧
        canonicalCorrection a p q n < 3 / (a n : ℝ) := by
  sorry

/-- States long243:eq:shiftedsign, long243:res:classicalhalfspace from the long record for Erdős
problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.canonical_growthDefect_identity in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_growthDefect_identity
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n) (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - 1 =
      -(((canonicalError a p q n : ℤ) : ℝ) /
          ((canonicalNaturalNumerator a p q n : ℕ) : ℝ)) +
        canonicalCorrection a p q n := by
  sorry

/-- States long243:res:strausbounded from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.original_coordinate_slow_growth_defect in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem original_coordinate_slow_growth_defect
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (δ : ℝ) (hδ : 0 < δ)
    (hslow : ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      productDefect a n ≤ (1 - δ) / (q : ℝ) *
        recordLogLog ((prefixProduct a n : ℝ) / (a n : ℝ))) :
    ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1 := by
  sorry

/-- States long243:res:strausbounded from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.prefix_ratio_le_canonicalNumerator in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem prefix_ratio_le_canonicalNumerator
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ))) (n : ℕ) :
    (prefixProduct a n : ℝ) / (a n : ℝ) ≤
      ((canonicalNaturalNumerator a p q n : ℕ) : ℝ) := by
  sorry

/-- States long243:res:frontier, res:frontier from the long record and the short record for
Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR7.canonical_frontier in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_frontier
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n →
      (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (∃ N, ∀ n, N ≤ n → E n ≠ 0) ∧
    Tendsto (fun n ↦ |(E n : ℝ)| / (C n : ℝ)) atTop (nhds 0) ∧
    (∀ N B : ℕ, ∃ n, N ≤ n ∧ E n < -(B : ℤ)) ∧
    Tendsto (fun N ↦ ∑ n ∈ Finset.range N,
      max (-(E n : ℝ)) 0 / (C n : ℝ)) atTop atTop := by
  sorry

/-- States long243:res:tailratio from the long record for Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR7.canonical_tail_ratio_quantitative in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_tail_ratio_quantitative
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    let C := canonicalNaturalNumerator a p q
    (∃ N, ∀ n, N ≤ n →
      |(C (n + 1) : ℝ) / (C n : ℝ) -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ 16 / (a n : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n, N ≤ n →
      Real.exp (c * (2 : ℝ) ^ n) ≤ (a n : ℝ)) := by
  sorry

/-- States long243:res:mass, res:mass, res:massscalar from the long record and the short record
for Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR7.finite_negative_mass_paper in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_negative_mass_paper :
    (∀ (C : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) →
      (∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n) →
      Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) →
      ∃ N, ∀ n, N ≤ n → E n = 0) ∧
    (∀ (a C D : ℕ → ℕ) (E : ℕ → ℤ),
      (∀ n, 0 < C n) →
      (∀ n, C (n + 1) + D n = a n * C n) →
      (∀ n, D (n + 1) = a n * D n) →
      (∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)) →
      Summable (fun n ↦ max (-(E n : ℝ)) 0 / (C n : ℝ)) →
      ∃ N, ∀ n, N ≤ n →
        (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) := by
  sorry

end Erdos249257.ExternalVerification243PaperStatementsL
