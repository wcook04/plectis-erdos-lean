/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.HalfCylinderIntegerGreedy
import Erdos249257.TwentyOneQuotientCompactness
import Erdos249257.TwentyOneQuotientGreedy
import Solutions.PalomarCorpus.E257ba.Statement

open Filter
open Set
open scoped Classical
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsBA

theorem twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows
    {R : ℕ → ℕ}
    (hR : Tendsto R atTop atTop)
    (hrow : ∀ k : ℕ,
      2 ≤ R k ∧
        twentyOneEvenQuotientGreedyRemainder (R k) ≤ 2 ^ (R k)) :
    TwentyOneCofinalEvenQuotientGreedyDecay := @Erdos249257.twentyOneCofinalEvenQuotientGreedyDecay_of_closedRows R hR hrow

end PalomarCorpus.E257.PaperStatementsBA
