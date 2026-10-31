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
`Erdos249257.HalfCylinderIntegerGreedy`,
`ErdosProblems.Erdos257.PaperCompleteR21.GreedyOrbitNoTies`,
`ErdosProblems.Erdos257.PaperCompleteR21.SeamPrefixStabilityLimit`.
-/

open Filter
open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresBV

noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2

noncomputable def listGreedyRemAfter : ℕ → List ℕ → ℕ → ℕ
  | 0, _, C => C
  | _ + 1, [], C => C
  | m + 1, w :: ws, C => listGreedyRemAfter m ws (if w ≤ C then C - w else C)

noncomputable def seamIntRem (s m : ℕ) : ℕ :=
  listGreedyRemAfter m (seamWeights s) (seamSubsetTarget s)

noncomputable def seamScaledTarget (s : ℕ) : ℝ :=
  (seamSubsetTarget s : ℝ) / (4 : ℝ) ^ s

noncomputable def seamScaledWeight (s d : ℕ) : ℝ :=
  (truncatedMersenneWeight s d : ℝ) / (4 : ℝ) ^ s

noncomputable def tailGreedyRemainder (t : ℝ) (v : ℕ → ℝ) : ℕ → ℝ
  | 0 => t
  | m + 1 =>
      if v (m + 1 + 1) ≤ tailGreedyRemainder t v m then
        tailGreedyRemainder t v m - v (m + 1 + 1)
      else tailGreedyRemainder t v m

/-- States thm:seam-limit from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.seamScaledRem_eq_tailGreedyRemainder in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem seamScaledRem_eq_tailGreedyRemainder {s : ℕ} (hs : 2 ≤ s) :
    ∀ m : ℕ, m ≤ s - 2 →
      ((seamIntRem s m : ℕ) : ℝ) / (4 : ℝ) ^ s
        = tailGreedyRemainder (seamScaledTarget s) (seamScaledWeight s) m := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresBV
