/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.BooleanMobiusGlobalRepair
import ErdosProblems.Erdos257.PaperCompleteR21.CompatibleFiniteRowFamily

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusGlobalRepair`,
`ErdosProblems.Erdos257.PaperCompleteR21.CompatibleFiniteRowFamily`.
-/

open Filter
open Set
open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresT

structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d

noncomputable def globalRepairLimitBit
    (T : BooleanMobiusGlobalRepairTrajectory) (d : ℕ) : Bool :=
  T.bit (2 * d) d

noncomputable def globalRepairLimitSupport
    (T : BooleanMobiusGlobalRepairTrajectory) : Set ℕ :=
  {d : ℕ | 2 ≤ d ∧ globalRepairLimitBit T d = true}

noncomputable def globalRepairStageSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun d ↦ bit n d = true

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied structure `BooleanMobiusGlobalRepairTrajectory` and its source `Erdos249257.BooleanMobiusGlobalRepairTrajectory` carry the same
fields, so each converts into the other field by field. -/
def BooleanMobiusGlobalRepairTrajectory_transport_toSrc (x : BooleanMobiusGlobalRepairTrajectory) :
    Erdos249257.BooleanMobiusGlobalRepairTrajectory :=
  ⟨x.bit, x.frozen_step⟩

/-- The inverse of `BooleanMobiusGlobalRepairTrajectory_transport_toSrc`. -/
def BooleanMobiusGlobalRepairTrajectory_transport_ofSrc (x : Erdos249257.BooleanMobiusGlobalRepairTrajectory) :
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

end Erdos249257.ExternalVerification257PaperStructuresT
