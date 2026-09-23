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
`Erdos249257.GreedyAchievementSet`, `Erdos249257.HalfCutLocator`.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

namespace Erdos249257.ExternalVerification257PaperStructuresU

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d

/-- States lem:rank-step-trichotomy from the long record for Erdős problem #257. Transported
from Erdos249257.IsStraddlePrefix.half_step_forced in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem IsStraddlePrefix.half_step_forced {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    (IsStraddlePrefix (1 / 2 : ℝ) u (d + 1) ∧
        ¬ IsStraddlePrefix (1 / 2 : ℝ) (insert (d + 1) u) (d + 1)) ∨
      (IsStraddlePrefix (1 / 2 : ℝ) (insert (d + 1) u) (d + 1) ∧
          ¬ IsStraddlePrefix (1 / 2 : ℝ) u (d + 1)) ∨
        (positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
            < 1 / 2 ∧
          (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
            + mersenneWeight (d + 1)) := by
  sorry

/-- States lem:rank-step-trichotomy from the long record for Erdős problem #257. Transported
from Erdos249257.isStraddlePrefix_step_trichotomy in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem isStraddlePrefix_step_trichotomy {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix t u d) :
    IsStraddlePrefix t u (d + 1) ∨
      IsStraddlePrefix t (insert (d + 1) u) (d + 1) ∨
        (positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t ∧
          t < positiveMersenneSupportValue (↑u : Set ℕ)
              + mersenneWeight (d + 1)) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresU
