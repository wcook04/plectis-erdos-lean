/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257: general identities for perturbed greedy recurrences

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open scoped BigOperators
open Matrix
open Filter
open Set
open Topology

namespace PalomarCorpus.E257.PaperStructuresBU
open scoped BigOperators
/-- Local definition PerturbedFamily, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure PerturbedFamily (α : Type*) where
  oldSum : α → ℕ
  pulse : α → ℕ
  gap : ℕ
  pulseCap : ℕ
  gap_pos : 0 < gap
  pulse_le : ∀ x, pulse x ≤ pulseCap
  oldSum_injective : Function.Injective oldSum
  separated : ∀ {x y}, oldSum x < oldSum y →
    oldSum x + gap ≤ oldSum y
  pulseCap_lt_three_gap : pulseCap < 3 * gap
/-- Local definition AdjacentCut, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure PerturbedFamily.AdjacentCut {α : Type*} (F : PerturbedFamily α) (C : ℕ) where
  below : α
  above : α
  below_admissible : F.oldSum below ≤ C
  below_maximal : ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below
  above_strict : C < F.oldSum above
  above_minimal : ∀ x, C < F.oldSum x → F.oldSum above ≤ F.oldSum x
/-- Local definition abovePulse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.abovePulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.above
/-- Local definition overshoot, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.overshoot {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.oldSum K.above - C
/-- Local definition successorCarries, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.successorCarries {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : Prop :=
  4 * K.overshoot + K.abovePulse ≤ F.gap
/-- Local definition prefixChoice, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.prefixChoice {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) [Decidable K.successorCarries] : α :=
  if K.successorCarries then K.above else K.below
/-- States record:257bm-i15 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.prefixChoice_eq_below in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem prefixChoice_eq_below {α : Type*} (F : PerturbedFamily α) {C : ℕ}
    (K : F.AdjacentCut C) [Decidable K.successorCarries]
    (h : ¬ K.successorCarries) :
    K.prefixChoice = K.below := by
  sorry
end PalomarCorpus.E257.PaperStructuresBU

namespace PalomarCorpus.E257.PaperStructuresO
open Matrix
/-- A finite or infinite coefficient word together with a binary-normalized reverse carry. The intended equation is `bit m + 2 * carry m = coeff m + carry (m + 1)`. No Boolean hypothesis is built into the structure: the overlap theorem needs only the explicit seam and overlap bits that it consumes. Local copy of Erdos249257.HalfTrappingReturnCarry.ReverseCarryWord, restated so the compared statements elaborate against Mathlib alone. -/
structure ReverseCarryWord where
  coeff : ℕ → ℤ
  bit : ℕ → ℤ
  carry : ℕ → ℤ
  normalized : ∀ m : ℕ,
    bit m + 2 * carry m = coeff m + carry (m + 1)
/-- Carry difference between two reverse-carry words. Local copy of Erdos249257.HalfTrappingReturnCarry.carryDifference, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryDifference (left right : ReverseCarryWord) (m : ℕ) : ℤ :=
  left.carry m - right.carry m
/-- States record:257bm-i16 from the long record for Erdős problem #257. Transported from Erdos249257.HalfTrappingReturnCarry.overlappingMidpointReturns_twoPow_le_realBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem overlappingMidpointReturns_twoPow_le_realBound
    (left right : ReverseCarryWord) (N M : ℕ) (bound : ℝ) (hN : 1 ≤ N)
    (hNM : M ≤ 2 * N - 2)
    (hcoeffSeam : left.coeff (M + 1) = right.coeff (M + 1))
    (hleftSeam : left.bit (M + 1) = 1)
    (hrightSeam : right.bit (M + 1) = 0)
    (hcoeffOverlap : ∀ j < 2 * N - M - 1,
      left.coeff (M + 2 + j) = right.coeff (M + 2 + j))
    (hbitOverlap : ∀ j < 2 * N - M - 1,
      left.bit (M + 2 + j) = right.bit (M + 2 + j))
    (hleftNonneg : 0 ≤ left.carry (2 * N + 1))
    (hrightNonneg : 0 ≤ right.carry (2 * N + 1))
    (hleftBound : (left.carry (2 * N + 1) : ℝ) ≤ bound)
    (hrightBound : (right.carry (2 * N + 1) : ℝ) ≤ bound) :
    (2 : ℝ) ^ (2 * N - M - 1) ≤ bound := by
  sorry
/-- States record:257bm-i16 from the long record for Erdős problem #257. Transported from Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem overlappingReverseCarryWords_carryDifference_eq_twoPow_mul_odd
    (left right : ReverseCarryWord) (seam length : ℕ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j)) :
    ∃ z : ℤ, Odd z ∧
      carryDifference left right (seam + 1 + length) =
        (2 : ℤ) ^ length * z := by
  sorry
/-- States record:257bm-i16 from the long record for Erdős problem #257. Transported from Erdos249257.HalfTrappingReturnCarry.overlappingReverseCarryWords_twoPow_le_realBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem overlappingReverseCarryWords_twoPow_le_realBound
    (left right : ReverseCarryWord) (seam length : ℕ) (bound : ℝ)
    (hcoeffSeam : left.coeff seam = right.coeff seam)
    (hleftSeam : left.bit seam = 1)
    (hrightSeam : right.bit seam = 0)
    (hcoeffOverlap : ∀ j < length,
      left.coeff (seam + 1 + j) = right.coeff (seam + 1 + j))
    (hbitOverlap : ∀ j < length,
      left.bit (seam + 1 + j) = right.bit (seam + 1 + j))
    (hleftNonneg : 0 ≤ left.carry (seam + 1 + length))
    (hrightNonneg : 0 ≤ right.carry (seam + 1 + length))
    (hleftBound : (left.carry (seam + 1 + length) : ℝ) ≤ bound)
    (hrightBound : (right.carry (seam + 1 + length) : ℝ) ≤ bound) :
    (2 : ℝ) ^ length ≤ bound := by
  sorry
end PalomarCorpus.E257.PaperStructuresO

namespace PalomarCorpus.E257.PaperStatementsAL
open Filter
open Set
open Topology
/-- A Boolean support word through exponent `N`. Index zero is retained so restriction is literal; admissibility forces exponents zero and one off. Local copy of Erdos249257.HalfCarryReachability.HalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool
/-- The set represented by a finite Boolean word. Local copy of Erdos249257.HalfCarryReachability.wordSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}
/-- Append one Boolean bit to a finite half word. Local copy of Erdos249257.HalfCarrySelectedWindow.extendHalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def extendHalfWord {N : ℕ} (a : HalfWord N) (β : Bool) : HalfWord (N + 1) :=
  Fin.lastCases β a
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- States record:257bm-i17 from the long record for Erdős problem #257. Transported from Erdos249257.HalfCylinderFiniteShadow.supportCoeff_insert_divisor in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supportCoeff_insert_divisor
    (A : Set ℕ) {d n : ℕ} (hd : d ∈ n.divisors) (hdA : d ∉ A) :
    supportCoeff (insert d A) n = supportCoeff A n + 1 := by
  sorry
/-- States record:257bm-i17 from the long record for Erdős problem #257. Transported from Erdos249257.HalfDivisorUnitDrop.supportCoeff_boundaryPair_unitDrop_at_double in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supportCoeff_boundaryPair_unitDrop_at_double
    {N : ℕ} (a : HalfWord N) (left right : HalfWord (N + 1))
    (hleft : left = extendHalfWord a true)
    (hright : right = extendHalfWord a false) :
    supportCoeff (wordSupport left) (2 * (N + 1)) =
      supportCoeff (wordSupport right) (2 * (N + 1)) + 1 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAL
