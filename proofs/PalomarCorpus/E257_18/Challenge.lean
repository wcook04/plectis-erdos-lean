/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record section 6.2: exact identities and reductions (part 1 of 6)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open ArithmeticFunction
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
open scoped Classical
open scoped BigOperators

namespace PalomarCorpus.E257_18.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- Real greedy residual after processing exponents `1, ..., n`. Local copy of Erdos249257.greedyMersenneRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n
/-- The set of ranks selected by the greedy Mersenne rule on x, namely the positive m for which the weight at m is at most the greedy remainder after rank m minus 1. -/
noncomputable def greedyMersenneSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧
    mersenneWeight m ≤ greedyMersenneRemainder x (m - 1)}
/-- The positive exponents omitted by the real greedy recursion. Local copy of Erdos249257.greedyMersenneSkippedSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def greedyMersenneSkippedSupport (x : ℝ) : Set ℕ :=
  {m : ℕ | m ≠ 0 ∧ m ∉ greedyMersenneSupport x}
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
end PalomarCorpus.E257_18.Shared

namespace PalomarCorpus.E257.PaperStatementsAJ
open ArithmeticFunction
/-- States thm:mobius-lambert-identity from the long record for Erdős problem #257. Transported from MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_moebius_div_two_pow_sub_one_eq_half :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAJ

namespace PalomarCorpus.E257.PaperStatementsAQ
open ArithmeticFunction
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_18.Shared (mersenneWeight)
/-- The Boolean support term selected by the negative Möbius sign. Local copy of Erdos249257.MobiusSignSupportNoGo.negativeMobiusTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def negativeMobiusTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = -1 then mersenneWeight (d : ℕ) else 0
/-- The positive Möbius tail, with the exceptional `d = 1` term removed. Local copy of Erdos249257.MobiusSignSupportNoGo.positiveMobiusTailTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMobiusTailTerm (d : ℕ+) : ℝ :=
  if moebius (d : ℕ) = 1 ∧ (d : ℕ) ≠ 1 then mersenneWeight (d : ℕ) else 0
/-- States cor:negative-mobius-overshoot from the long record for Erdős problem #257. Transported from Erdos249257.MobiusSignSupportNoGo.half_lt_tsum_negativeMobius in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_lt_tsum_negativeMobius :
    (1 : ℝ) / 2 < ∑' d : ℕ+, negativeMobiusTerm d := by
  sorry
/-- States cor:negative-mobius-overshoot from the long record for Erdős problem #257. Transported from Erdos249257.MobiusSignSupportNoGo.tsum_negativeMobius_eq_half_add_positiveMobiusTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_negativeMobius_eq_half_add_positiveMobiusTail :
    (∑' d : ℕ+, negativeMobiusTerm d) =
      1 / 2 + ∑' d : ℕ+, positiveMobiusTailTerm d := by
  sorry
end PalomarCorpus.E257.PaperStatementsAQ

namespace PalomarCorpus.E257.PaperStatementsAH
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_18.Shared (mersenneWeight)
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The Erdős-Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
/-- States thm:half-skip-dichotomy from the long record for Erdős problem #257. Transported from Erdos249257.irrational_erdosBorweinMersenneConstant in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_erdosBorweinMersenneConstant :
    Irrational erdosBorweinMersenneConstant := by
  sorry
end PalomarCorpus.E257.PaperStatementsAH

namespace PalomarCorpus.E257.PaperStatementsB
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_18.Shared (greedyMersenneRemainder greedyMersenneSkippedSupport greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
/-- States record:257bm-c20, thm:half-skip-dichotomy from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_greedySkippedSupport_infinite :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := by
  sorry
end PalomarCorpus.E257.PaperStatementsB

namespace PalomarCorpus.E257.PaperStatementsG
open Set
open Filter
open scoped ENNReal
open MeasureTheory
open Topology
open scoped Classical
export PalomarCorpus.E257_18.Shared (greedyMersenneRemainder greedyMersenneSkippedSupport greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
/-- `M` is the final exponent skipped by the actual greedy half orbit. Local copy of Erdos249257.IsLastHalfGreedySkip, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsLastHalfGreedySkip (M : ℕ) : Prop :=
  M ∈ greedyMersenneSkippedSupport (1 / 2 : ℝ) ∧
    ∀ m, M < m → m ∉ greedyMersenneSkippedSupport (1 / 2 : ℝ)
/-- States thm:nine-way-hub from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_no_lastHalfGreedySkip :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ ∃ M : ℕ, IsLastHalfGreedySkip M := by
  sorry
end PalomarCorpus.E257.PaperStatementsG

namespace PalomarCorpus.E257.PaperStructuresBJ
open Set
open Filter
open scoped BigOperators
open scoped ENNReal
open MeasureTheory
open Topology
export PalomarCorpus.E257_18.Shared (greedyMersenneRemainder greedyMersenneSkippedSupport greedyMersenneSupport mersenneAchievementSet mersenneWeight positiveMersenneSupportValue)
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
/-- Local definition terminal, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def terminal {s : ℕ} (hs : 3 ≤ s) (b : SeamRowWord (s + 1)) : Bool :=
  b ⟨s - 2, by omega⟩
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
/-- Local definition SeamGreedyCofinalTerminalFalse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamGreedyCofinalTerminalFalse : Prop :=
  ∃ p : ℕ → ℕ, ∃ hp5 : ∀ j, 5 ≤ p j,
    Tendsto p atTop atTop ∧
      ∀ j, terminal
          (by have := hp5 j; omega)
          (seamGreedyWord (p j + 1)) = false
/-- Local definition SeamGreedyEventuallyRight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamGreedyEventuallyRight : Prop :=
  ∃ S : ℕ, 5 ≤ S ∧
    ∀ s : ℕ, S ≤ s →
      seamGreedyWord (s + 1) = (seamGreedyWord s).extend true
/-- Local definition SeamGreedyUnboundedSkippedRanksAlong, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamGreedyUnboundedSkippedRanksAlong (rows : ℕ → ℕ) : Prop :=
  ∃ skip : ∀ j, Fin (rows j - 2),
    Tendsto rows atTop atTop ∧
      Tendsto (fun j => ((skip j : ℕ) + 2)) atTop atTop ∧
        ∀ j, seamGreedyWord (rows j) (skip j) = false
/-- Local definition SeamGreedyUnboundedTerminalFalse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamGreedyUnboundedTerminalFalse : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, ∃ hp5 : 5 ≤ p,
    N ≤ p ∧
      terminal (by omega)
        (seamGreedyWord (p + 1)) = false
/-- States thm:nine-way-hub from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_cofinalTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyCofinalTerminalFalse := by
  sorry
/-- States thm:nine-way-hub from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_exists_unboundedSkippedRanksAlong :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ∃ rows : ℕ → ℕ, SeamGreedyUnboundedSkippedRanksAlong rows := by
  sorry
/-- States thm:nine-way-hub from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_not_seamGreedyEventuallyRight :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      ¬ SeamGreedyEventuallyRight := by
  sorry
/-- States thm:nine-way-hub from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_unboundedTerminalFalse :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔
      SeamGreedyUnboundedTerminalFalse := by
  sorry
/-- States thm:nine-way-hub from the long record for Erdős problem #257. Transported from Erdos249257.unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unboundedTerminalFalse_iff_greedyMersenneSkippedSupport_infinite :
    SeamGreedyUnboundedTerminalFalse ↔
      (greedyMersenneSkippedSupport (1 / 2 : ℝ)).Infinite := by
  sorry
end PalomarCorpus.E257.PaperStructuresBJ
