/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup
import ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser
import ErdosProblems.Erdos243.PaperCompleteR11.QuantitativeRecordDichotomy
import ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState
import ErdosProblems.Erdos243.PrimitiveRecordBarrier
import ErdosProblems.Erdos243.ReciprocalTailRigidity

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup`,
`ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser`,
`ErdosProblems.Erdos243.PaperCompleteR11.QuantitativeRecordDichotomy`,
`ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState`,
`ErdosProblems.Erdos243.PrimitiveRecordBarrier`,
`ErdosProblems.Erdos243.ReciprocalTailRigidity`.
-/

open Filter
open scoped Topology
open scoped BigOperators

namespace Erdos249257.ExternalVerification243PaperStatementsM

noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2

noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)

noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop

noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

theorem canonical_recordTheta_eq_zero_iff
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)) :
    recordTheta (canonicalNaturalNumerator a p q) = 0 ↔
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR11.canonical_recordTheta_eq_zero_iff a ha hapos p q hq hs hgrowth

theorem canonical_recordTheta_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    (1 : EReal) < recordTheta (canonicalNaturalNumerator a p q) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR11.canonical_recordTheta_gt_one a ha hapos p q hq hs hgrowth hnot

theorem canonical_recordTheta_zero_or_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)) :
    recordTheta (canonicalNaturalNumerator a p q) = 0 ∨
      (1 : EReal) < recordTheta (canonicalNaturalNumerator a p q) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR11.canonical_recordTheta_zero_or_gt_one a ha hapos p q hq hs hgrowth

end Erdos249257.ExternalVerification243PaperStatementsM
