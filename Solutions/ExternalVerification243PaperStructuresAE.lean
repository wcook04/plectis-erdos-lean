/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup
import ErdosProblems.Erdos243.PaperCompleteR11.LogLogNormaliser
import ErdosProblems.Erdos243.PaperCompleteR21.ExactOrbitRecordDichotomy
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
`ErdosProblems.Erdos243.PaperCompleteR21.ExactOrbitRecordDichotomy`,
`ErdosProblems.Erdos243.PrimitiveRecordBarrier`,
`ErdosProblems.Erdos243.ReciprocalTailRigidity`.
-/

open Filter
open scoped Topology

namespace Erdos249257.ExternalVerification243PaperStructuresAE

noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2

noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)

noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop

noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos243.runningMax` is the same function. -/
theorem runningMax_transport_def : @runningMax = @ErdosProblems.Erdos243.runningMax := by
  first
  | (rfl; done)
  | (simp only [runningMax, ErdosProblems.Erdos243.runningMax]; done)
  | (with_unfolding_all rfl; done)
  | (unfold runningMax ErdosProblems.Erdos243.runningMax; done)
  | (unfold runningMax ErdosProblems.Erdos243.runningMax <;> simp only [ErdosProblems.Erdos243.runningMax, *]; done)
  | (ext x; simp only [runningMax, ErdosProblems.Erdos243.runningMax]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [runningMax, ErdosProblems.Erdos243.runningMax]; done)
  | (funext a; fun_induction runningMax a <;> simp only [ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a; induction a <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a; induction a <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a; induction a <;> simp [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a; simp [runningMax, ErdosProblems.Erdos243.runningMax]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [runningMax, ErdosProblems.Erdos243.runningMax]; done)
  | (funext a b; fun_induction runningMax a b <;> simp only [ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b; induction b <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b; induction a generalizing b <;> simp [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b; induction b generalizing a <;> simp [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b; simp [runningMax, ErdosProblems.Erdos243.runningMax]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [runningMax, ErdosProblems.Erdos243.runningMax]; done)
  | (funext a b c; fun_induction runningMax a b c <;> simp only [ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b c; induction c <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [runningMax, ErdosProblems.Erdos243.runningMax, *]; done)
  | (funext a b c; simp [runningMax, ErdosProblems.Erdos243.runningMax]; done)
  | (simp [runningMax, ErdosProblems.Erdos243.runningMax]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge` is the same function. -/
theorem recordLogLogCharge_transport_def : @recordLogLogCharge = @ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge := by
  first
  | (rfl; done)
  | (simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold recordLogLogCharge ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge; done)
  | (unfold recordLogLogCharge ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge <;> simp only [ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (ext x; simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def]; done)
  | (funext a; fun_induction recordLogLogCharge a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a; induction a <;> simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a; induction a <;> simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a; induction a <;> simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a; simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def]; done)
  | (funext a b; fun_induction recordLogLogCharge a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b; simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def]; done)
  | (funext a b c; fun_induction recordLogLogCharge a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def, *]; done)
  | (funext a b c; simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def]; done)
  | (simp [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def] <;> rfl; done)
  | (funext v1; unfold recordLogLogCharge ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge <;> simp only [runningMax_transport_def] <;> rfl; done)
  | (funext v1; unfold recordLogLogCharge ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge <;> (repeat' (first | rw [runningMax_transport_def])) <;> rfl; done)
  | (funext v1 v2; simp only [recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, runningMax_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold recordLogLogCharge ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge <;> simp only [runningMax_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold recordLogLogCharge ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge <;> (repeat' (first | rw [runningMax_transport_def])) <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos243.PaperCompleteR11.recordTheta` is the same function. -/
theorem recordTheta_transport_def : @recordTheta = @ErdosProblems.Erdos243.PaperCompleteR11.recordTheta := by
  first
  | (rfl; done)
  | (simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold recordTheta ErdosProblems.Erdos243.PaperCompleteR11.recordTheta; done)
  | (unfold recordTheta ErdosProblems.Erdos243.PaperCompleteR11.recordTheta <;> simp only [ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (ext x; simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def]; done)
  | (funext a; fun_induction recordTheta a <;> simp only [ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a; induction a <;> simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a; induction a <;> simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a; induction a <;> simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a; simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def]; done)
  | (funext a b; fun_induction recordTheta a b <;> simp only [ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b; simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def]; done)
  | (funext a b c; fun_induction recordTheta a b c <;> simp only [ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def, *]; done)
  | (funext a b c; simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def]; done)
  | (simp [recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, runningMax_transport_def, recordLogLogCharge_transport_def]; done)

theorem exactOrbit_one_le_recordTheta
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    (1 : EReal) ≤ recordTheta C := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_one_le_recordTheta a C D E ha hCpos hD0 hC hD hE hvanish hnot

theorem exactOrbit_recordTheta_gt_one
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (ha : ∀ n, 1 < a n) (hCpos : ∀ n, 0 < C n) (hD0 : 1 ≤ D 0)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hE : ∀ n, E n = centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n → K * Int.natAbs (E n) < C n)
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → E n = 0) :
    (1 : EReal) < recordTheta C := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_recordTheta_gt_one a C D E ha hCpos hD0 hC hD hE hvanish hnot

end Erdos249257.ExternalVerification243PaperStructuresAE
