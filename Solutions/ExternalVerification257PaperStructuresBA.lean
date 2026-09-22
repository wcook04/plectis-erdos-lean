/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.BooleanMobiusCriticalCapacityCofinal
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.GreedyAchievementSet

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

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied structure `ProtectedExactLocalMersenneRow` and its source `Erdos249257.ProtectedExactLocalMersenneRow` carry the same
fields, so each converts into the other field by field. -/
def ProtectedExactLocalMersenneRow_transport_toSrc (x : ProtectedExactLocalMersenneRow) :
    Erdos249257.ProtectedExactLocalMersenneRow :=
  ⟨x.endpoint, x.cutoff, x.support, x.core, x.endpoint_six, x.cutoff_four, x.core_subset, x.new_above_cutoff, x.core_bounds, x.support_bounds, x.exact_quotient, x.core_below_half, x.two_mem_core, x.endpoint_lt_twice_cutoff⟩

/-- The inverse of `ProtectedExactLocalMersenneRow_transport_toSrc`. -/
def ProtectedExactLocalMersenneRow_transport_ofSrc (x : Erdos249257.ProtectedExactLocalMersenneRow) :
    ProtectedExactLocalMersenneRow :=
  ⟨x.endpoint, x.cutoff, x.support, x.core, x.endpoint_six, x.cutoff_four, x.core_subset, x.new_above_cutoff, x.core_bounds, x.support_bounds, x.exact_quotient, x.core_below_half, x.two_mem_core, x.endpoint_lt_twice_cutoff⟩

@[simp] theorem ProtectedExactLocalMersenneRow_transport_toSrc_endpoint
    (x : ProtectedExactLocalMersenneRow) :
    (ProtectedExactLocalMersenneRow_transport_toSrc x).endpoint = x.endpoint := rfl

@[simp] theorem ProtectedExactLocalMersenneRow_transport_ofSrc_endpoint
    (x : Erdos249257.ProtectedExactLocalMersenneRow) :
    (ProtectedExactLocalMersenneRow_transport_ofSrc x).endpoint = x.endpoint := rfl

@[simp] theorem ProtectedExactLocalMersenneRow_transport_toSrc_cutoff
    (x : ProtectedExactLocalMersenneRow) :
    (ProtectedExactLocalMersenneRow_transport_toSrc x).cutoff = x.cutoff := rfl

@[simp] theorem ProtectedExactLocalMersenneRow_transport_ofSrc_cutoff
    (x : Erdos249257.ProtectedExactLocalMersenneRow) :
    (ProtectedExactLocalMersenneRow_transport_ofSrc x).cutoff = x.cutoff := rfl

@[simp] theorem ProtectedExactLocalMersenneRow_transport_toSrc_support
    (x : ProtectedExactLocalMersenneRow) :
    (ProtectedExactLocalMersenneRow_transport_toSrc x).support = x.support := rfl

@[simp] theorem ProtectedExactLocalMersenneRow_transport_ofSrc_support
    (x : Erdos249257.ProtectedExactLocalMersenneRow) :
    (ProtectedExactLocalMersenneRow_transport_ofSrc x).support = x.support := rfl

@[simp] theorem ProtectedExactLocalMersenneRow_transport_toSrc_core
    (x : ProtectedExactLocalMersenneRow) :
    (ProtectedExactLocalMersenneRow_transport_toSrc x).core = x.core := rfl

@[simp] theorem ProtectedExactLocalMersenneRow_transport_ofSrc_core
    (x : Erdos249257.ProtectedExactLocalMersenneRow) :
    (ProtectedExactLocalMersenneRow_transport_ofSrc x).core = x.core := rfl

theorem exists_laterProtectedExactLocalMersenneRow
    (hcap : SkippedCoreCriticalQuotientSupply)
    (s : ProtectedExactLocalMersenneRow) :
    ∃ t : ProtectedExactLocalMersenneRow, s.endpoint < t.endpoint := by
  obtain ⟨w, hw⟩ := @Erdos249257.exists_laterProtectedExactLocalMersenneRow hcap (ProtectedExactLocalMersenneRow_transport_toSrc s)
  refine ⟨ProtectedExactLocalMersenneRow_transport_ofSrc w, ?_⟩
  simpa only [ProtectedExactLocalMersenneRow_transport_ofSrc_endpoint, ProtectedExactLocalMersenneRow_transport_ofSrc_cutoff, ProtectedExactLocalMersenneRow_transport_ofSrc_support, ProtectedExactLocalMersenneRow_transport_ofSrc_core] using hw

end Erdos249257.ExternalVerification257PaperStructuresBA
