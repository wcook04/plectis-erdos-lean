/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.HalfCylinderIntegerGreedy
import Solutions.PalomarCorpus.E257c.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsC

theorem remainder_lt_gap_iff_eq_integerGreedyBits
    {gap C : ℕ} {weights : List ℕ} {bits : List Bool} (hgap : 0 < gap)
    (hdom : GapDominates gap weights)
    (hlen : bits.length = weights.length)
    (hadm : weightedBoolSum weights bits ≤ C) :
    C - weightedBoolSum weights bits < gap ↔
      bits = integerGreedyBits weights C ∧
        integerGreedyRemainder weights C < gap := by
  set_option smartUnfolding false in
  exact @Erdos249257.BooleanMobiusGreedyReduction.remainder_lt_gap_iff_eq_integerGreedyBits gap C weights bits hgap hdom hlen hadm

end PalomarCorpus.E257.PaperStatementsC
