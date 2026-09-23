/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_19

Every non-theorem declaration of `PalomarCorpus/E257_19/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open scoped BigOperators

namespace PalomarCorpus.E257.PaperStructuresBH
open Filter
open Set
open scoped BigOperators
/-- Structural part of an endpoint-by-endpoint repair trajectory. The arithmetic producer receipts are separated into `GlobalBooleanMobiusRepairFeasible` below. Local copy of Erdos249257.BooleanMobiusGlobalRepairTrajectory, restated so the compared statements elaborate against Mathlib alone. -/
structure BooleanMobiusGlobalRepairTrajectory where
  bit : ℕ → ℕ → Bool
  frozen_step : ∀ {n d : ℕ}, 2 * d ≤ n → bit (n + 1) d = bit n d
/-- Local definition signedDyadicValue, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def signedDyadicValue : List ℤ → ℤ
  | [] => 0
  | z :: zs => z + 2 * signedDyadicValue zs
/-- The finite Boolean support displayed by row `n`. Coordinates zero and one are normalized away at the definition boundary. Local copy of Erdos249257.globalRepairStageSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairStageSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (Finset.Icc 2 n).filter fun d ↦ bit n d = true
/-- Local definition upperSuffixWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def upperSuffixWord (a : ℕ → ℕ) (R M : ℕ) : List ℕ :=
  List.map (fun i ↦ a (M - i)) (List.range (M - R))
/-- Local definition globalRepairUpperWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def globalRepairUpperWord
    (T : BooleanMobiusGlobalRepairTrajectory) (n : ℕ) : List ℕ :=
  upperSuffixWord
    (fun d ↦ if T.bit n d = true then 1 else 0) (n / 2) n
/-- The part of row `n` which is already frozen before its upper-half rewrite. Local copy of Erdos249257.globalRepairLowerSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def globalRepairLowerSupport (bit : ℕ → ℕ → Bool) (n : ℕ) : Finset ℕ :=
  (globalRepairStageSupport bit n).filter fun d ↦ d ≤ n / 2
/-- The local integer Mersenne quotient at binary scale M and rank d, namely the natural number quotient of 2 to the power M by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)
/-- The total local quotient carried by a finite set D of ranks at binary scale M, namely the sum over d in D of the local Mersenne quotient at M and d. -/
noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d
/-- Local definition upperHalfRepairLength, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def upperHalfRepairLength (n : ℕ) : ℕ :=
  n - n / 2
/-- The divisor incidence of a finite set D of ranks at n, namely the number of members of D that divide n. -/
noncomputable def endpointDivisorContribution (D : Finset ℕ) (n : ℕ) : ℕ :=
  (D.filter fun d ↦ d ∣ n).card
/-- The carry left after reading the nonterminating binary expansion of `2⁻ᵏ` through place `M` and subtracting the quotient contributions of `D`. The theorem below proves that the truncating natural subtraction is honest in the endpoint situation where it is used. Local copy of Erdos249257.localBinarySuffix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localBinarySuffix (D : Finset ℕ) (k M : ℕ) : ℕ :=
  2 ^ (M - k) - localPrefixQuotient D M - 1
/-- Local definition GlobalEndpointExponentialBound, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def GlobalEndpointExponentialBound
    (T : BooleanMobiusGlobalRepairTrajectory) : Prop :=
  ∀ n : ℕ, 2 ≤ n →
    let D := globalRepairLowerSupport T.bit n
    2 ^ (endpointDivisorContribution D n - 1) - 1 ≤
      localBinarySuffix D 1 (n - 1)
/-- The next signed Boolean--Möbius coefficient supplied by the binary carry recurrence. Local copy of Erdos249257.localRepairInteger, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def localRepairInteger (D : Finset ℕ) (k n : ℕ) : ℤ :=
  2 * (localBinarySuffix D k (n - 1) : ℤ) + 1 -
    (endpointDivisorContribution D n : ℤ)
/-- Local definition GlobalBooleanMobiusRepairFeasible, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def GlobalBooleanMobiusRepairFeasible
    (T : BooleanMobiusGlobalRepairTrajectory) : Prop :=
  GlobalEndpointExponentialBound T ∧
  (∀ n : ℕ, 2 ≤ n →
    let D := globalRepairLowerSupport T.bit n
    signedDyadicValue
        (List.map (fun b : ℕ ↦ (b : ℤ)) (globalRepairUpperWord T n)) =
      localRepairInteger D 1 n) ∧
  (∀ n : ℕ, 2 ≤ n →
    let D := globalRepairLowerSupport T.bit n
    localRepairInteger D 1 n < (2 ^ upperHalfRepairLength n : ℕ)) ∧
  (∀ n : ℕ, 2 ≤ n →
    localPrefixQuotient (globalRepairStageSupport T.bit n) n =
      2 ^ (n - 1) - 1)
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
/-- Local definition belowPulse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.belowPulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.below
/-- Local definition overshoot, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.overshoot {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.oldSum K.above - C
/-- Local definition remainder, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.remainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := C - F.oldSum K.below
/-- Local definition successorCarries, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.successorCarries {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : Prop :=
  4 * K.overshoot + K.abovePulse ≤ F.gap
/-- Local definition terminalWeight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def PerturbedFamily.AdjacentCut.terminalWeight {α : Type*} {F : PerturbedFamily α} {C : ℕ} (_K : F.AdjacentCut C) : ℕ := 2 * F.gap + 4
/-- Local definition SeamRowWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool
/-- Local definition ofList, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)
/-- Local definition toNatWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SeamRowWord.toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false
/-- The truncated integer Mersenne weight at seam row s and rank d, namely the natural number quotient of 4 to the power s by 2 to the power d minus 1; at d = 0 the divisor is 0 and the value is 0. -/
noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)
/-- Local definition wordWeightSum, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def wordWeightSum (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then truncatedMersenneWeight s (i + 2) else 0
/-- The quotient pulse contributed by rank d between consecutive seam rows at row s, namely 1 if d divides 2s+2, plus twice 1 if d divides 2s+1, and 0 for the nondividing cases. -/
noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)
/-- Local definition wordPulse, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def wordPulse (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then rowPulse s (i + 2) else 0
/-- The integer capacity of the seam subset sum problem at row s, namely 2 raised to the exponent 2s minus 1, less 2 to the power s; both the exponent subtraction and the outer subtraction are truncated natural subtraction, so the value is 0 at s = 0 and at s = 1. -/
noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s
/-- The greedy Boolean word for an integer subset sum problem: given a list of weights in the order presented and a capacity, take a weight when it is at most the current capacity and subtract it, otherwise skip it and keep the capacity. -/
noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C
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
/-- Local definition seamWordSupport, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def seamWordSupport {s : ℕ} (b : SeamRowWord s) : Finset ℕ :=
  ((Finset.univ : Finset (Fin (s - 2))).filter (fun i => b i = true)).image
    (fun i : Fin (s - 2) => (i : ℕ) + 2)
/-- Local definition IsLargestFalseRank, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def IsLargestFalseRank {s : ℕ} (b : SeamRowWord s) (d : ℕ) : Prop :=
  2 ≤ d ∧ d < s ∧
    d ∉ seamWordSupport b ∧
      ∀ e : ℕ, d < e → e < s → e ∈ seamWordSupport b
/-- The paper's row-weight functional `W_s(E) = ∑_{e ∈ E} ⌊4^s/(2^e − 1)⌋`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.rowWeightSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rowWeightSum (s : ℕ) (E : Finset ℕ) : ℤ :=
  ∑ e ∈ E, ⌊(4 : ℝ) ^ s / ((2 : ℝ) ^ e - 1)⌋
end PalomarCorpus.E257.PaperStructuresBH
