/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.DyadicPrefixCompression`, `Erdos249257.GreedyAchievementSet`,
`Erdos249257.HalfCutLocator`.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

namespace Erdos249257.ExternalVerification257PaperStructuresCN

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def nextDyadicExcessIntNumerator (p : ℤ) (n L : ℕ) : ℤ :=
  ((2 ^ n : ℕ) : ℤ) * p - (L : ℤ)

/-- States lem:rank-step-trichotomy from the long record for Erdős problem #257. Transported
from Erdos249257.IsStraddlePrefix.half_strict in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem IsStraddlePrefix.half_strict {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix (1 / 2 : ℝ) u d) :
    positiveMersenneSupportValue (↑u : Set ℕ) < 1 / 2 ∧
      (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
        + mersenneTail d := by
  sorry

/-- States lem:dyadic-excess-reformulation from the long record for Erdős problem #257.
Transported from Erdos249257.divInt_mem_nextMersenneDyadicSliver_iff_excess in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem divInt_mem_nextMersenneDyadicSliver_iff_excess
    (p : ℤ) (n L : ℕ) (hL : 0 < L) :
    (1 / (2 : ℚ) ^ (n + 1) < Rat.divInt p ((2 * L : ℕ) : ℤ) ∧
        Rat.divInt p ((2 * L : ℕ) : ℤ) < mersenneWeightRat (n + 1)) ↔
      (0 < nextDyadicExcessIntNumerator p n L ∧
        2 * nextDyadicExcessIntNumerator p n L < p) := by
  sorry

/-- States lem:rank-step-trichotomy from the long record for Erdős problem #257. Transported
from Erdos249257.positiveMersenneSupportValue_insert in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem positiveMersenneSupportValue_insert {F : Finset ℕ} {a : ℕ}
    (ha : a ∉ F) :
    positiveMersenneSupportValue (↑(insert a F) : Set ℕ)
      = mersenneWeight a + positiveMersenneSupportValue (↑F : Set ℕ) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresCN
