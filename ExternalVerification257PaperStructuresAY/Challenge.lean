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
`Erdos249257.BooleanMobiusGreedyReduction`, `Erdos249257.BooleanMobiusLocalRepair`,
`Erdos249257.HalfCylinderIntegerGreedy`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresAY

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localMersenneWeightsFrom (M R : ℕ) : ℕ → List ℕ
  | d =>
      if h : d ≤ R then
        localMersenneQuotient M d :: localMersenneWeightsFrom M R (d + 1)
      else
        []
termination_by d => R + 1 - d
decreasing_by omega

noncomputable def localMersenneWeights (M R : ℕ) : List ℕ :=
  localMersenneWeightsFrom M R 2

noncomputable def lowerBinaryWindow (M R : ℕ) : ℕ :=
  2 ^ (M - R)

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

/-- States record:257bm-i11c from the long record for Erdős problem #257. Transported from
Erdos249257.BooleanMobiusGreedyReduction.localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem localMersenneHalfTarget_lower_word_eq_greedy_and_remainder_eq
    {M R A : ℕ} {bits : List Bool}
    (hRM : R ≤ M)
    (hlen : bits.length = (localMersenneWeights M R).length)
    (hfill :
      weightedBoolSum (localMersenneWeights M R) bits + A =
        2 ^ (M - 1) - 1)
    (hA : A < lowerBinaryWindow M R) :
    bits = integerGreedyBits (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) ∧
      A = integerGreedyRemainder (localMersenneWeights M R)
        (2 ^ (M - 1) - 1) := by
  sorry

/-- States record:257bm-i11b from the long record for Erdős problem #257. Transported from
Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeightsFrom_gapDominates in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem localMersenneWeightsFrom_gapDominates
    {M R d : ℕ} (hRM : R ≤ M) (hd : 1 ≤ d) :
    GapDominates (lowerBinaryWindow M R)
      (localMersenneWeightsFrom M R d) := by
  sorry

/-- States record:257bm-i11b from the long record for Erdős problem #257. Transported from
Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_even in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem localMersenneWeights_gapDominates_even
    (R : ℕ) (hR : 1 ≤ R) :
    GapDominates (2 ^ (R - 1)) (localMersenneWeights (2 * R - 1) R) := by
  sorry

/-- States record:257bm-i11b from the long record for Erdős problem #257. Transported from
Erdos249257.BooleanMobiusGreedyReduction.localMersenneWeights_gapDominates_odd in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem localMersenneWeights_gapDominates_odd (R : ℕ) :
    GapDominates (2 ^ R) (localMersenneWeights (2 * R) R) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresAY
