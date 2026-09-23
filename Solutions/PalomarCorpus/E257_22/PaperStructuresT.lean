/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusGlobalRepair
import ErdosProblems.Erdos257.PaperCompleteR21.CompatibleFiniteRowFamily
import Solutions.PalomarCorpus.E257_22.Statement

open Filter
open Set
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresT
export PalomarCorpus.E257_22.Shared (BooleanMobiusGlobalRepairTrajectory globalRepairStageSupport)

noncomputable def BooleanMobiusGlobalRepairTrajectory_transport_toSrc (x : BooleanMobiusGlobalRepairTrajectory) :
    Erdos249257.BooleanMobiusGlobalRepairTrajectory :=
  ⟨x.bit, x.frozen_step⟩

/-- The inverse of `BooleanMobiusGlobalRepairTrajectory_transport_toSrc`. -/
noncomputable def BooleanMobiusGlobalRepairTrajectory_transport_ofSrc (x : Erdos249257.BooleanMobiusGlobalRepairTrajectory) :
    BooleanMobiusGlobalRepairTrajectory :=
  ⟨x.bit, x.frozen_step⟩

@[simp] theorem BooleanMobiusGlobalRepairTrajectory_transport_toSrc_bit
    (x : BooleanMobiusGlobalRepairTrajectory) :
    (BooleanMobiusGlobalRepairTrajectory_transport_toSrc x).bit = x.bit := rfl

@[simp] theorem BooleanMobiusGlobalRepairTrajectory_transport_ofSrc_bit
    (x : Erdos249257.BooleanMobiusGlobalRepairTrajectory) :
    (BooleanMobiusGlobalRepairTrajectory_transport_ofSrc x).bit = x.bit := rfl

theorem paper_compatible_rows_agree_with_limit
    (T : BooleanMobiusGlobalRepairTrajectory) {n d : ℕ} (hd : d ≤ n / 2) :
    d ∈ globalRepairStageSupport T.bit n ↔ d ∈ globalRepairLimitSupport T := @ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_rows_agree_with_limit (BooleanMobiusGlobalRepairTrajectory_transport_toSrc T) n d hd

end PalomarCorpus.E257.PaperStructuresT
