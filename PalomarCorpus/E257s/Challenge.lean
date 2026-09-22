/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band s

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace PalomarCorpus.E257.PaperStructuresS
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- **Packet §4.** A finite support word certified to straddle the target at depth `d`: the coded value is at most `t` and the value plus the complete unresolved tail mass still reaches `t`. This is deliberately *weaker* than the `HalfPrefixForcingChain.interval_trapped` containment condition: overlap of the correction image with the cylinder, not containment inside it. Local copy of Erdos249257.IsStraddlePrefix, restated so the compared statements elaborate against Mathlib alone. -/
structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sidedness in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_one_sidedness :
    (∃ P : ℕ → Prop, ComputablePred P ∧
        ((1 / 2 : ℝ) ∉ mersenneAchievementSet ↔ ∃ n : ℕ, P n) ∧
        ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ∀ n : ℕ, ¬ P n)) ∧
      (∀ d : ℕ, ∃ x : ℝ, IsStraddlePrefix x ∅ d ∧ x ∉ mersenneAchievementSet) := by
  sorry
end PalomarCorpus.E257.PaperStructuresS
