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
`Erdos249257.BooleanMobiusGlobalRepair`, `Erdos249257.BooleanMobiusLocalRepair`,
`ErdosProblems.Erdos257.PaperCompleteR21.CompatibleFiniteRowFamily`.
-/

open Filter
open Set
open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresAW

structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d

noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card

noncomputable def globalRepairStageSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun d ↦ bit n d = true

noncomputable def globalRepairLowerSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (globalRepairStageSupport bit n).filter fun d ↦ d ≤ n / 2

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1

noncomputable def localRepairInteger (D : Finset ℕ) (k n : ℕ) : ℤ :=
  2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
    (endpointDivisorContribution D n : ℤ)

/-- States record:257bm-c3 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_compatible_first_condition_gives_nonneg in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_compatible_first_condition_gives_nonneg
    (T : BooleanMobiusGlobalRepairTrajectory)
    (hbound : ∀ n : ℕ, 2 ≤ n →
      2 ^ (endpointDivisorContribution (globalRepairLowerSupport T.bit n) n - 1)
          - 1 ≤
        localBinarySuffix (globalRepairLowerSupport T.bit n) 1 (n - 1))
    {n : ℕ} (hn : 2 ≤ n) :
    0 ≤ localRepairInteger (globalRepairLowerSupport T.bit n) 1 n := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresAW
