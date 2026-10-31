/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.BooleanMobiusGreedyReduction
import Erdos249257.HalfCylinderIntegerGreedy

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusGreedyReduction`, `Erdos249257.HalfCylinderIntegerGreedy`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStatementsC

noncomputable def GapDominates (gap : ℕ) : List ℕ → Prop
  | [] => True
  | w :: ws => gap + ws.sum ≤ w ∧ GapDominates gap ws

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0

noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

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

end Erdos249257.ExternalVerification257PaperStatementsC
