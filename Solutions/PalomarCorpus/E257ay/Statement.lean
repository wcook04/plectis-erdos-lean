/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257ay

Every non-theorem declaration of `PalomarCorpus/E257ay/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E257.PaperStructuresAY
open scoped BigOperators
/-- The integral part of `2^M / (2^d - 1)`. Local copy of Erdos249257.localMersenneQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- Descending local quotient weights with ranks `d,d+1,…,R`. Local copy of Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneWeightsFrom (M R : ℕ) : ℕ → List ℕ
  | d =>
      if h : d ≤ R then
        localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1)
      else
        []
termination_by d => R + 1 - d
decreasing_by omega
/-- The complete lower quotient word on ranks `2,…,R`. Local copy of Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localMersenneWeights (M R : ℕ) : List ℕ :=
  localMersenneWeightsFrom M R 2
/-- Number of binary suffix values available after a truncation at depth `M`, when ranks through `R` have already been fixed. Local copy of Erdos249257.BooleanMobiusGreedyReduction.lowerBinaryWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lowerBinaryWindow (M R : ℕ) : ℕ :=
  2 ^ (M - R)
/-- Every head exceeds the sum of its complete tail by at least `gap`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.GapDominates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GapDominates (gap : ℕ) : List ℕ → Prop
  | [] => True
  | w :: ws => gap + ws.sum ≤ w ∧ GapDominates gap ws
/-- Descending greedy subset for an integer capacity. Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- Weighted sum of a Boolean word. The equal-length hypotheses below make the two fallback equations irrelevant. Local copy of Erdos249257.HalfCylinderIntegerGreedy.weightedBoolSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0
/-- Local copy of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)
end PalomarCorpus.E257.PaperStructuresAY
