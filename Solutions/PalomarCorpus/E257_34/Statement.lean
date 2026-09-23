/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_34

Every non-theorem declaration of `PalomarCorpus/E257_34/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open Topology
open scoped BigOperators
open MeasureTheory
open scoped ENNReal

namespace PalomarCorpus.E257_34.Shared
/-- A Boolean support word through exponent `N`. Index zero is retained so restriction is literal; admissibility forces exponents zero and one off. Local copy of Erdos249257.HalfCarryReachability.HalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool
/-- The binary affine orbit driven by an integer sequence a from an initial value, defined by orbit 0 equal to the initial value and orbit (n+1) equal to twice orbit n minus a at n+1. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- The discrete square-root strip used by the half-carry search. Local copy of Erdos249257.HalfCarryReachability.halfStripBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4
/-- Local definition restrictWord, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def restrictWord {M N : ℕ} (hMN : M ≤ N) (a : HalfWord N) : HalfWord M :=
  fun i ↦ a ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hMN)⟩
/-- **The support coefficient** `f_A(n) = #{d ∣ n : d ∈ A}`, the Dirichlet incidence `1_A * 1` of a support set `A ⊆ ℕ`. This is the coefficient in which Erdős #257 is actually stated: `∑_{a∈A} 1/(b^a - 1) = ∑_n f_A(n)/b^n`. Full support gives `f_ℕ = τ`; primes give `ω`; prime powers give `Ω`. Local copy of Erdos249257.supportCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card
/-- The integer half carry attached to a support A, namely the binary affine orbit started at 1 and driven by the divisor incidence coefficients of A shifted by one, so that the orbit at n+1 is twice the orbit at n minus the number of divisors of n+2 lying in A; the shift and the recursion index compose, so the coefficient consumed at step n+1 is the one at n+2. -/
noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1
/-- Local definition supportSuffixNumeral, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def supportSuffixNumeral (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 =>
      2 * supportSuffixNumeral A M L +
        if M + L + 1 ∈ A then 1 else 0
/-- The set represented by a finite Boolean word. Local copy of Erdos249257.HalfCarryReachability.wordSupport, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}
/-- Local definition HalfStripAdmissible, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def HalfStripAdmissible (N : ℕ) (a : HalfWord N) : Prop :=
  a ⟨0, Nat.zero_lt_succ N⟩ = false ∧
  (∀ h : 1 < N + 1, a ⟨1, h⟩ = false) ∧
  ∀ n : ℕ, 1 ≤ n → n ≤ N →
    (1 : ℤ) ≤ integerHalfCarry (wordSupport a) (n - 1) ∧
      integerHalfCarry (wordSupport a) (n - 1) ≤ halfStripBound n
/-- Local definition SelectedHalfWindow, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure SelectedHalfWindow (N R : ℕ) where
  word : ∀ k : ℕ, 1 ≤ k → k ≤ R → HalfWord N
  admissible : ∀ k hk hkR, HalfStripAdmissible N (word k hk hkR)
  terminal : ∀ k hk hkR,
    integerHalfCarry (wordSupport (word k hk hkR)) (N - 1) = k
/-- Local definition wordSuffixNumeral, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def wordSuffixNumeral
    {N : ℕ} (a : HalfWord N) (M L : ℕ) : ℕ :=
  @supportSuffixNumeral (wordSupport a) (Classical.decPred _) M L
/-- Local definition HasSuffixCylinderAt, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def HasSuffixCylinderAt
    {M N R : ℕ} (W : SelectedHalfWindow N R) (hMN : M ≤ N)
    (endpoint : ℕ) : Prop :=
  ∃ pfx : HalfWord M,
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord hMN (W.word k hk hkR) = pfx ∧
        wordSuffixNumeral (W.word k hk hkR) M (N - M) + k =
          endpoint
/-- Local definition CylinderStage, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure CylinderStage (K N : ℕ) where
  hKN : K ≤ N
  window : SelectedHalfWindow N (halfStripBound N)
  endpoint : ℕ
  cylinder : HasSuffixCylinderAt window hKN endpoint
  covers : halfStripBound N ≤ endpoint
end PalomarCorpus.E257_34.Shared

namespace PalomarCorpus.E257.PaperStatementsQ
open Filter
open Set
open Topology
open scoped BigOperators
export PalomarCorpus.E257_34.Shared (affineBinaryOrbit integerHalfCarry supportCoeff)
/-- The canonical integer half carry measured relative to the signed Möbius solution. Index `N` corresponds to the packet's state `e_{N+1}`. Local copy of Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1
/-- The two fresh coefficient rows, measured relative to the three units contributed by the centred recurrence itself. Local copy of Erdos249257.pairedCenteredForcing, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pairedCenteredForcing (A : Set ℕ) (N : ℕ) : ℤ :=
  2 * (supportCoeff A (N + 2) : ℤ) +
    (supportCoeff A (N + 3) : ℤ) - 3
end PalomarCorpus.E257.PaperStatementsQ

namespace PalomarCorpus.E257.PaperStatementsBD
open Filter
open Set
export PalomarCorpus.E257_34.Shared (halfStripBound)
end PalomarCorpus.E257.PaperStatementsBD

namespace PalomarCorpus.E257.PaperStructuresBR
open Set
open Filter
open Topology
export PalomarCorpus.E257_34.Shared (CylinderStage HalfStripAdmissible HalfWord HasSuffixCylinderAt SelectedHalfWindow affineBinaryOrbit halfStripBound integerHalfCarry restrictWord supportCoeff supportSuffixNumeral wordSuffixNumeral wordSupport)
/-- Local definition EvenSeamReachable, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def EvenSeamReachable (δ c k : ℤ) : Prop :=
  (∃ h : ℤ, h ≤ δ ∧ (k = 2 * h - c - 1 ∨ k = 2 * h - c - 2)) ∨
  (∃ h : ℤ, δ < h ∧ (k = 2 * h - c ∨ k = 2 * h - c - 1))
/-- Append one Boolean bit to a finite half word. Local copy of Erdos249257.HalfCarrySelectedWindow.extendHalfWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def extendHalfWord {N : ℕ} (a : HalfWord N) (β : Bool) : HalfWord (N + 1) :=
  Fin.lastCases β a
/-- Local definition SelectedHalfInterval, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure SelectedHalfInterval (N L U : ℕ) where
  word : ∀ q : ℕ, L ≤ q → q ≤ U → HalfWord N
  admissible : ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
    HalfStripAdmissible N (word q hqL hqU)
  terminal : ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
    integerHalfCarry (wordSupport (word q hqL hqU)) (N - 1) = q
/-- Local definition HasSuffixCylinderOnInterval, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def HasSuffixCylinderOnInterval
    {M N L U : ℕ} (W : SelectedHalfInterval N L U)
    (hMN : M ≤ N) (endpoint : ℕ) : Prop :=
  ∃ pfx : HalfWord M,
    ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
      restrictWord hMN (W.word q hqL hqU) = pfx ∧
        wordSuffixNumeral (W.word q hqL hqU) M (N - M) + q = endpoint
/-- Local definition InStripTwoSheetStage, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure InStripTwoSheetStage (K N : ℕ) where
  hK1N : K + 1 ≤ N
  hole : ℕ
  hole_pos : 1 ≤ hole
  hole_le : hole ≤ halfStripBound N
  boundaryPrefix : HalfWord K
  lower : SelectedHalfWindow N (hole - 1)
  lowerCylinder : HasSuffixCylinderAt lower hK1N (hole - 1)
  lowerLiteral : ∀ q (hq : 1 ≤ q) (hqR : q ≤ hole - 1),
    restrictWord hK1N (lower.word q hq hqR) =
      extendHalfWord boundaryPrefix true
  upperEndpoint : ℕ
  upper : SelectedHalfInterval N (hole + 1) (halfStripBound N)
  upperCylinder : HasSuffixCylinderOnInterval upper hK1N upperEndpoint
  upperLiteral : ∀ q (hqL : hole + 1 ≤ q)
      (hqU : q ≤ halfStripBound N),
    restrictWord hK1N (upper.word q hqL hqU) =
      extendHalfWord boundaryPrefix false
  upperCovers : halfStripBound N ≤ upperEndpoint
  endpointSeparation : upperEndpoint =
    hole + 2 ^ (N - (K + 1))
  seamCut : ℕ
  seamCoeff : ℕ
  hole_eq : (hole : ℤ) = 2 * (seamCut : ℤ) - (seamCoeff : ℤ)
  scalar_exact (q : ℕ) (hq : 1 ≤ q)
      (hqB : q ≤ halfStripBound N) :
    EvenSeamReachable (seamCut : ℤ) (seamCoeff : ℤ) q ↔ q ≠ hole
end PalomarCorpus.E257.PaperStructuresBR

namespace PalomarCorpus.E257.PaperStructuresBT
open MeasureTheory
open Set
open Filter
open Topology
export PalomarCorpus.E257_34.Shared (CylinderStage HalfStripAdmissible HalfWord HasSuffixCylinderAt SelectedHalfWindow affineBinaryOrbit halfStripBound integerHalfCarry restrictWord supportCoeff supportSuffixNumeral wordSuffixNumeral wordSupport)
end PalomarCorpus.E257.PaperStructuresBT

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- One term of the binary coding of the achievement set. Local copy of Erdos249257.mersenneDigitTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)
/-- The support value coded by a binary sequence. Local copy of Erdos249257.positiveMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b
/-- Binary digit strings supported on `J`. Local copy of ErdosProblems.Erdos257.SupportedMersenneDigits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}
/-- The ordinary Mersenne digit map restricted to a chosen support. Local copy of ErdosProblems.Erdos257.supportedMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1
/-- The achievement set obtained by allowing digits only on `J`. Local copy of ErdosProblems.Erdos257.supportedMersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)
end PalomarCorpus.E257.PaperStatementsAM
