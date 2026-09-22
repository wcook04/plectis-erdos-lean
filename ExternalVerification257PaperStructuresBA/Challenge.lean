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
`Erdos249257.BooleanMobiusCriticalCapacityCofinal`, `Erdos249257.BooleanMobiusLocalRepair`,
`Erdos249257.GreedyAchievementSet`.
-/

open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresBA

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def localMersennePrefixValue (D : Finset ℕ) : ℚ :=
  ∑ d ∈ D, mersenneWeightRat d

structure ProtectedExactLocalMersenneRow where
  endpoint : ℕ
  cutoff : ℕ
  support : Finset ℕ
  core : Finset ℕ
  endpoint_six : 6 ≤ endpoint
  cutoff_four : 4 ≤ cutoff
  core_subset : core ⊆ support
  new_above_cutoff : ∀ d ∈ support, d ∉ core → cutoff < d
  core_bounds : ∀ d ∈ core, 2 ≤ d ∧ d ≤ cutoff
  support_bounds : ∀ d ∈ support, 2 ≤ d ∧ d ≤ endpoint
  exact_quotient :
    localPrefixQuotient support endpoint = 2 ^ (endpoint - 1) - 1
  core_below_half : localMersennePrefixValue core < (1 / 2 : ℚ)
  two_mem_core : 2 ∈ core
  endpoint_lt_twice_cutoff : endpoint < 2 * cutoff

noncomputable def SkippedCoreCriticalQuotientSupply : Prop :=
  ∀ (D : Finset ℕ) (c : ℕ),
    4 ≤ c →
    (∀ d ∈ D, 2 ≤ d ∧ d < c) →
    localMersennePrefixValue D < (1 / 2 : ℚ) →
    (1 / 2 : ℚ) - localMersennePrefixValue D < mersenneWeightRat c →
    2 ^ ((2 * c - 2) - 1) ≤
      localPrefixQuotient (insert c D) (2 * c - 2)

/-- States record:257bm-c5 from the long record for Erdős problem #257. Transported from
Erdos249257.exists_laterProtectedExactLocalMersenneRow in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem exists_laterProtectedExactLocalMersenneRow
    (hcap : SkippedCoreCriticalQuotientSupply)
    (s : ProtectedExactLocalMersenneRow) :
    ∃ t : ProtectedExactLocalMersenneRow, s.endpoint < t.endpoint := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresBA
