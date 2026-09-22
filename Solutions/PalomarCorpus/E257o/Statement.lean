/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257o

Every non-theorem declaration of `PalomarCorpus/E257o/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Matrix

namespace PalomarCorpus.E257.PaperStructuresO
open Matrix
/-- A finite or infinite coefficient word together with a binary-normalized reverse carry. The intended equation is `bit m + 2 * carry m = coeff m + carry (m + 1)`. No Boolean hypothesis is built into the structure: the overlap theorem needs only the explicit seam and overlap bits that it consumes. Local copy of Erdos249257.HalfTrappingReturnCarry.ReverseCarryWord, restated so the compared statements elaborate against Mathlib alone. -/
structure ReverseCarryWord where
  coeff : ℕ → ℤ
  bit : ℕ → ℤ
  carry : ℕ → ℤ
  normalized : ∀ m : ℕ,
    bit m + 2 * carry m = coeff m + carry (m + 1)
/-- Carry difference between two reverse-carry words. Local copy of Erdos249257.HalfTrappingReturnCarry.carryDifference, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryDifference (left right : ReverseCarryWord) (m : ℕ) : ℤ :=
  left.carry m - right.carry m
end PalomarCorpus.E257.PaperStructuresO
