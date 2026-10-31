/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record sections 5.2 to 5.5: what is proved; integer quotients and their remainder identity; a real-valued form of the quotient identity

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Topology
open Set
open scoped ENNReal
open MeasureTheory
open scoped BigOperators

namespace PalomarCorpus.E257_05.Shared
/-- The base b reciprocal power subseries supported on A, namely the sum over a in A of 1 divided by b to the power a minus 1, written as an unconditional sum of the indicator of A; the exponent a = 0 contributes 0 because division by zero is zero here, so membership of 0 in A does not change the value. -/
noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The Erdős-Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
end PalomarCorpus.E257_05.Shared

namespace PalomarCorpus.E257.PaperStatementsAG
open Filter
open Topology
export PalomarCorpus.E257_05.Shared (erdosSupportSeries)
/-- States thm:full-support, thm:full-support-catalogue from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSum_full_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSum_full_support (b : ℕ) (hb : 2 ≤ b) :
    Irrational (∑' k : ℕ, (1 : ℝ) / ((b : ℝ) ^ (k + 1) - 1)) := by
  sorry
/-- States thm:eventually-periodic from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSupportSeries_eventuallyPeriodic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_eventuallyPeriodic
    (b m N₀ : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, N₀ ≤ n → (n + m ∈ A ↔ n ∈ A))
    (hinf : A.Infinite) :
    Irrational (erdosSupportSeries b A) := by
  sorry
/-- States thm:residue-odd from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSupportSeries_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_odd (b : ℕ) (hb : 2 ≤ b) :
    Irrational (erdosSupportSeries b {n : ℕ | Odd n}) := by
  sorry
/-- States thm:periodic-support from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosSupportSeries_periodic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosSupportSeries_periodic
    (b m : ℕ) (A : Set ℕ) (hb : 2 ≤ b) (hm : 0 < m)
    (hper : ∀ n : ℕ, n + m ∈ A ↔ n ∈ A)
    (hpos : ∃ a : ℕ, 0 < a ∧ a ∈ A) :
    Irrational (erdosSupportSeries b A) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAG

namespace PalomarCorpus.E257.PaperStatementsBC
open Filter
open Topology
export PalomarCorpus.E257_05.Shared (erdosSupportSeries)
/-- States the paper statement it is bound to from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.irrational_residueClass_positive_support in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_residueClass_positive_support
    (b m : ℕ) (c : ℤ) (hb : 2 ≤ b) (hm : 1 ≤ m) :
    Irrational (erdosSupportSeries b
      {n : ℕ | 0 < n ∧ (n : ℤ) % (m : ℤ) = c % (m : ℤ)}) := by
  sorry
end PalomarCorpus.E257.PaperStatementsBC

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_05.Shared (erdosBorweinMersenneConstant mersenneTail mersenneWeight)
/-- States thm:real-form from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.mersenne_constant_decimal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenne_constant_decimal :
    (1066951524152917 : ℝ)/10^16 < erdosBorweinMersenneConstant-3/2 ∧
      erdosBorweinMersenneConstant-3/2 < (1066951524152918 : ℝ)/10^16 := by
  sorry
/-- States thm:topology from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.mersenne_topology_quantitative in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenne_topology_quantitative :
    |erdosBorweinMersenneConstant-(16067 : ℝ)/10000| < 1/20000 ∧
    1 < erdosBorweinMersenneConstant ∧
    Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ)^n*mersenneTail n) Filter.atTop (nhds 1) := by
  sorry
/-- States thm:real-form from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.row_constant_eq_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem row_constant_eq_tail :
    erdosBorweinMersenneConstant-3/2 = mersenneTail 1-1/2 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsB
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_05.Shared (mersenneTail mersenneWeight)
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- States thm:greedy-survival-record from the long record for Erdős problem #257. Transported from Erdos249257.greedy_survives_of_mem_mersenneAchievementSet in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem greedy_survives_of_mem_mersenneAchievementSet {x : ℝ}
    (hx : x ∈ mersenneAchievementSet) :
    0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  sorry
/-- States thm:greedy-survival-catalogue, thm:greedy-survival-record from the long record for Erdős problem #257. Transported from Erdos249257.mem_mersenneAchievementSet_iff_greedy_survival in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mem_mersenneAchievementSet_iff_greedy_survival (x : ℝ) :
    x ∈ mersenneAchievementSet ↔
      0 ≤ x ∧ ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n := by
  sorry
/-- States thm:greedy-survival-record from the long record for Erdős problem #257. Transported from Erdos249257.mem_mersenneAchievementSet_of_greedy_survival in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mem_mersenneAchievementSet_of_greedy_survival {x : ℝ} (hx : 0 ≤ x)
    (hsurvive : ∀ n : ℕ, greedyMersenneRemainder x n ≤ mersenneTail n) :
    x ∈ mersenneAchievementSet := by
  sorry
end PalomarCorpus.E257.PaperStatementsB

namespace PalomarCorpus.E257.PaperStatementsAA
/-- States thm:master-identity from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.paper_master_identity_floors in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_master_identity_floors {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ((2 : ℤ)^(2*n-1) - (2 : ℤ)^n -
      ∑ d ∈ D, ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋) - (2 : ℤ)^n =
    ((2 : ℤ)^(2*n-1) -
      ∑ d ∈ Finset.Ico 2 (2*n+1), ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋) +
      ∑ d ∈ (Finset.Ico 2 n) \ D, ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋ := by
  sorry
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAR
open Filter
open Set
open scoped ENNReal
open MeasureTheory
open Topology
open scoped BigOperators
export PalomarCorpus.E257_05.Shared (erdosBorweinMersenneConstant mersenneTail mersenneWeight)
/-- The exact integer weight contributed at seam rank `s` by selecting a proper divisor rank `d < s`. Local copy of Erdos249257.HalfCylinderIntegerGreedy.truncatedMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- Delta for a selected prefix. This applies in particular to the integer greedy take set; the identity itself needs no greediness hypothesis. Local copy of ErdosProblems.Erdos257.PaperCompleteR20.rowDeviation, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowDeviation (n : ℕ) (D : Finset ℕ) : ℤ :=
  (2 : ℤ)^(2*n-1) - (2 : ℤ)^(n+1) - ∑ d ∈ D, (truncatedMersenneWeight n d : ℤ)
/-- States thm:real-form from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_core in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_real_quotient_core {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ∃ eta : ℝ,
      (rowDeviation n D : ℝ) = (4 : ℝ)^n *
        ((∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) -
          (erdosBorweinMersenneConstant-3/2)) + eta ∧
      0 < eta ∧ eta < (n : ℝ)+2/3 ∧ |eta| < 2*(n : ℝ)+2 := by
  sorry
/-- States thm:real-form from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.paper_real_quotient_margins in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_real_quotient_margins {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) (H : ℝ) :
    ((H+(2*(n : ℝ)+2))/(4 : ℝ)^n <
      |(∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) - (erdosBorweinMersenneConstant-3/2)| →
      H < |(rowDeviation n D : ℝ)|) ∧
    (H < |(rowDeviation n D : ℝ)| →
      (H-(2*(n : ℝ)+2))/(4 : ℝ)^n <
      |(∑ d ∈ (Finset.Ico 2 n) \ D, mersenneWeight d) - (erdosBorweinMersenneConstant-3/2)|) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAR
