/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusCriticalCapacityCofinal
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.GreedyAchievementSet
import Solutions.PalomarCorpus.E257ba.Statement

open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresBA

/-- The copied structure `ProtectedExactLocalMersenneRow` and its source `Erdos249257.ProtectedExactLocalMersenneRow` carry the same
fields, so each converts into the other field by field. -/
noncomputable def ProtectedExactLocalMersenneRow_transport_toSrc (x : ProtectedExactLocalMersenneRow) :
    Erdos249257.ProtectedExactLocalMersenneRow :=
  ⟨x.endpoint, x.cutoff, x.support, x.core, x.endpoint_six, x.cutoff_four, x.core_subset, x.new_above_cutoff, x.core_bounds, x.support_bounds, x.exact_quotient, x.core_below_half, x.two_mem_core, x.endpoint_lt_twice_cutoff⟩

/-- The inverse of `ProtectedExactLocalMersenneRow_transport_toSrc`. -/
noncomputable def ProtectedExactLocalMersenneRow_transport_ofSrc (x : Erdos249257.ProtectedExactLocalMersenneRow) :
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

end PalomarCorpus.E257.PaperStructuresBA
