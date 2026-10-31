/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record section 6.2: exact identities and reductions (part 2 of 6)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Set
open Filter
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology

namespace PalomarCorpus.E257_20.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
end PalomarCorpus.E257_20.Shared

namespace PalomarCorpus.E257.PaperStructuresBJ
open Set
open Filter
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- Local definition SeamRowWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local definition extend, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.extend {s : ℕ} (b : SeamRowWord s) (beta : Bool) :
    SeamRowWord (s + 1) :=
  fun i => if h : (i : ℕ) < s - 2 then b ⟨i, h⟩ else beta
/-- Local definition ofList, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- The greedy Boolean word for an integer subset sum problem: given a list of weights in the order presented and a capacity, take a weight when it is at most the current capacity and subtract it, otherwise skip it and keep the capacity. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
/-- Local definition integerGreedyBits_length, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def integerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (integerGreedyBits weights C).length = weights.length := by
  induction weights generalizing C with
  | nil => simp [integerGreedyBits]
  | cons w ws ih =>
      simp only [integerGreedyBits]
      split <;> simp [ih]
/-- The integer capacity of the seam subset sum problem at row s, namely 2 raised to the exponent 2s minus 1, less 2 to the power s; both the exponent subtraction and the outer subtraction are truncated natural subtraction, so the value is 0 at s = 0 and at s = 1. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The truncated integer Mersenne weight at seam row s and rank d, namely the natural number quotient of 4 to the power s by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- The list of truncated Mersenne weights at seam row s for the ranks from the given starting index up to s minus 1, in increasing rank order. -/
noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega
/-- The seam weight list at row s, namely the truncated Mersenne weights for ranks 2 up to s minus 1. -/
noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2
/-- Local definition seamWeightsFrom_eq_cons, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom_eq_cons {s d : ℕ} (h : d < s) :
    seamWeightsFrom s d =
      truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1) := by
  rw [seamWeightsFrom]
  simp [h]
/-- Local definition seamWeightsFrom_eq_nil, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom_eq_nil {s d : ℕ} (h : s ≤ d) :
    seamWeightsFrom s d = [] := by
  rw [seamWeightsFrom]
  simp [Nat.not_lt.mpr h]
/-- Local definition seamWeightsFrom_length_eq, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWeightsFrom_length_eq (s d : ℕ) :
    (seamWeightsFrom s d).length = s - d := by
  by_cases hds : d < s
  · rw [seamWeightsFrom_eq_cons hds, List.length_cons,
      seamWeightsFrom_length_eq s (d + 1)]
    omega
  · rw [seamWeightsFrom_eq_nil (by omega)]
    simp
    omega
termination_by s - d
decreasing_by omega
/-- Local definition seamWeights_length_eq, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  unfold seamWeights
  exact seamWeightsFrom_length_eq s 2
/-- Local definition seamGreedyWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])
/-- Local definition seamWordSupport, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
/-- States lem:eventually-right-impossible from the long record for Erdős problem #257. Transported from Erdos249257.prefix_add_mersenneTail_lt_half_of_eventually_right in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prefix_add_mersenneTail_lt_half_of_eventually_right
    {S D : ℕ} {u : Finset ℕ}
    (hS5 : 5 ≤ S) (hDS : D < S)
    (hu : ∀ e ∈ u, 2 ≤ e ∧ e < D)
    (hright : ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true)
    (hbase : seamWordSupport (seamGreedyWord S) =
      u ∪ Finset.Ico (D + 1) S) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail D <
      (1 / 2 : ℝ) := by
  sorry
end PalomarCorpus.E257.PaperStructuresBJ

namespace PalomarCorpus.E257.PaperStatementsAH
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight)
/-- The first two geometric channels of the Mersenne tail. This cap is strictly weaker than the dyadic cap while still lying below the full tail. Local copy of Erdos249257.halfTwoChannelCap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfTwoChannelCap (n : ℕ) : ℝ :=
  ((1 : ℝ) / 2) ^ n
    + (1 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.halfTwoChannelCap_lt_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem halfTwoChannelCap_lt_mersenneTail (n : ℕ) :
    halfTwoChannelCap n < mersenneTail n := by
  sorry
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.mersenneTail_eq_weight_add in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneTail_eq_weight_add (n : ℕ) :
    mersenneTail n = mersenneWeight (n + 1) + mersenneTail (n + 1) := by
  sorry
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.mersenneTail_le_two_mul_weight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneTail_le_two_mul_weight (n : ℕ) :
    mersenneTail n ≤ 2 * mersenneWeight (n + 1) := by
  sorry
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.mersenneTail_lt_weight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneTail_lt_weight {n : ℕ} (hn : 0 < n) :
    mersenneTail n < mersenneWeight n := by
  sorry
/-- States lem:mersenne-tail-weight from the long record for Erdős problem #257. Transported from Erdos249257.two_mul_mersenneWeight_succ_lt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_mul_mersenneWeight_succ_lt {n : ℕ} (hn : 0 < n) :
    2 * mersenneWeight (n + 1) < mersenneWeight n := by
  sorry
end PalomarCorpus.E257.PaperStatementsAH

namespace PalomarCorpus.E257.PaperStructuresU
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- **Packet §4.** A finite support word certified to straddle the target at depth `d`: the coded value is at most `t` and the value plus the complete unresolved tail mass still reaches `t`. This is deliberately *weaker* than the `HalfPrefixForcingChain.interval_trapped` containment condition: overlap of the correction image with the cylinder, not containment inside it. Local copy of Erdos249257.IsStraddlePrefix, restated so the compared statements elaborate against Mathlib alone. -/
structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
/-- States lem:rank-step-trichotomy from the long record for Erdős problem #257. Transported from Erdos249257.IsStraddlePrefix.half_step_forced in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
/-- States lem:rank-step-trichotomy from the long record for Erdős problem #257. Transported from Erdos249257.isStraddlePrefix_step_trichotomy in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem isStraddlePrefix_step_trichotomy {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : IsStraddlePrefix t u d) :
    IsStraddlePrefix t u (d + 1) ∨
      IsStraddlePrefix t (insert (d + 1) u) (d + 1) ∨
        (positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t ∧
          t < positiveMersenneSupportValue (↑u : Set ℕ)
              + mersenneWeight (d + 1)) := by
  sorry
end PalomarCorpus.E257.PaperStructuresU

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- States lem:half-endpoint-kills from the long record for Erdős problem #257. Transported from Erdos249257.half_ne_coe_finset_add_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_ne_coe_finset_add_mersenneTail
    (u : Finset ℕ) (d : ℕ) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
      ≠ (1 / 2 : ℝ) := by
  sorry
/-- States lem:half-endpoint-kills from the long record for Erdős problem #257. Transported from Erdos249257.positiveMersenneSupportValue_coe_finset_ne_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem positiveMersenneSupportValue_coe_finset_ne_half
    {u : Finset ℕ} (h0 : 0 ∉ u) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≠ (1 / 2 : ℝ) := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.depth_prefix_interval_disjoint in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem depth_prefix_interval_disjoint {t : ℝ} {u v : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d) (hv : ∀ n ∈ v, 0 < n ∧ n ≤ d)
    (hut : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d)
    (hvt : positiveMersenneSupportValue (↑v : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑v : Set ℕ) + mersenneTail d) :
    u = v := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_endpoint_bounds in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_gap_endpoint_bounds {A : Set ℕ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hagree : ∀ n : ℕ, 0 < n → n ≤ d → (n ∈ A ↔ n ∈ u)) :
    (d + 1 ∉ A →
        positiveMersenneSupportValue A
          ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)) ∧
      (d + 1 ∈ A →
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)
          ≤ positiveMersenneSupportValue A) := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_excludes_every_representation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_gap_excludes_every_representation {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    ∀ A : Set ℕ, 0 ∉ A → positiveMersenneSupportValue A ≠ t := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_within_prefix_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_gap_within_prefix_interval {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d := by
  sorry
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStatementsD
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The set of positive exponents selected by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The positive exponents omitted by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSkippedSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- States thm:last-skip-iff-fatal from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_iff_every_actual_skip_survives in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_iff_every_actual_skip_survives :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∀ M : ℕ,
        M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) →
          greedyMersenneRemainder (1 / 2 : ℝ) M ≤ mersenneTail M := by
  sorry
end PalomarCorpus.E257.PaperStatementsD
