/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257t

Every non-theorem declaration of `PalomarCorpus/E257t/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open scoped BigOperators

namespace PalomarCorpus.E257.PaperStructuresT
open Filter
open Set
open scoped BigOperators
/-- Structural part of an endpoint-by-endpoint repair trajectory. The arithmetic producer receipts are separated into `GlobalBooleanMobiusRepairFeasible` below. Local copy of Erdos249257.BooleanMobiusGlobalRepairTrajectory, restated so the compared statements elaborate against Mathlib alone. -/
structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d
/-- The diagonal limit bit: inspect coordinate `d` at the first row after which the upper-half rewrites can no longer touch it. Local copy of Erdos249257.globalRepairLimitBit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairLimitBit
    (T : BooleanMobiusGlobalRepairTrajectory) (d : ℕ) : Bool :=
  T.bit (2 * d) d
/-- The positive frozen support selected by the diagonal limit word. Local copy of Erdos249257.globalRepairLimitSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairLimitSupport
    (T : BooleanMobiusGlobalRepairTrajectory) : Set ℕ :=
  {d : ℕ | 2 ≤ d ∧ globalRepairLimitBit T d = true}
/-- The finite Boolean support displayed by row `n`. Coordinates zero and one are normalized away at the definition boundary. Local copy of Erdos249257.globalRepairStageSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairStageSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun d ↦ bit n d = true
end PalomarCorpus.E257.PaperStructuresT
