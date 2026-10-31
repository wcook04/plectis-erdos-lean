/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup
import ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser
import ErdosProblems.Erdos243.PaperCompleteR21.SlowGrowthProductIncrements
import ErdosProblems.Erdos243.PrimitiveRecordBarrier

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup`,
`ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser`,
`ErdosProblems.Erdos243.PaperCompleteR21.SlowGrowthProductIncrements`,
`ErdosProblems.Erdos243.PrimitiveRecordBarrier`.
-/

open Filter
open scoped Topology

namespace Erdos249257.ExternalVerification243PaperStatementsR

noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2

noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)

noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop

theorem recordTheta_le_of_slow_negative
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ))
    (c : ℝ) (hc0 : 0 ≤ c) (N : ℕ)
    (hslow : ∀ n, N ≤ n → -((E n : ℤ) : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ)) :
    recordTheta C ≤ ((c : ℝ) : EReal) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.recordTheta_le_of_slow_negative a C D E hstep hE c hc0 N hslow

end Erdos249257.ExternalVerification243PaperStatementsR
