/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.HalfCylinderIntegerGreedy
import Solutions.PalomarCorpus.E257_27.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStructuresCJ

theorem above_newSum_le_capacity_iff {α : Type*} (F : PerturbedFamily α) {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) :
    F.newSum K.above ≤ K.newCapacity ↔ K.successorCarries := @Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.above_newSum_le_capacity_iff α F F C K

theorem below_newSum_le_capacity {α : Type*} (F : PerturbedFamily α) {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C)
    (hcap : F.pulseCap < F.gap) :
    F.newSum K.below ≤ K.newCapacity := @Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.below_newSum_le_capacity α F F C K hcap

theorem nextRemainder_trichotomy {α : Type*} (F : PerturbedFamily α) {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C)
    [Decidable K.successorCarries] :
    K.nextRemainder =
      if K.successorCarries then
        F.gap - (4 * K.overshoot + K.abovePulse)
      else if 4 * K.remainder + F.gap - K.belowPulse < K.terminalWeight then
        4 * K.remainder + F.gap - K.belowPulse
      else
        4 * K.remainder - F.gap - K.belowPulse - 4 := @Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.nextRemainder_trichotomy α F F C K inferInstance

theorem prefixChoice_maximal {α : Type*} (F : PerturbedFamily α) {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C)
    (hcap : F.pulseCap < F.gap)
    [Decidable K.successorCarries]
    {x : α} (hx : F.newSum x ≤ K.newCapacity) :
    F.newSum x ≤ F.newSum K.prefixChoice := @Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.prefixChoice_maximal α F F C K hcap inferInstance x hx

theorem prefixRemainder_eq_capacity_sub_choice {α : Type*} (F : PerturbedFamily α) {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C)
    [Decidable K.successorCarries] :
    K.prefixRemainder = K.newCapacity - F.newSum K.prefixChoice := @Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut.prefixRemainder_eq_capacity_sub_choice α F F C K inferInstance

end PalomarCorpus.E257.PaperStructuresCJ
