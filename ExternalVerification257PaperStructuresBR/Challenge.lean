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
`Erdos249257.CertificateKernel`, `Erdos249257.GenericTailOrbitRigidity`,
`Erdos249257.HalfCarryReachability`, `Erdos249257.HalfCarryRewindPhase`,
`Erdos249257.HalfCarrySelectedWindow`, `Erdos249257.SelectedSuffixCylinder`,
`Erdos249257.SuffixCylinderInStrip`, `Erdos249257.SuffixCylinderThreshold`,
`ErdosProblems.Erdos257.PaperCompleteR21.FeedbackRowStripWitnessAllDepths`.
-/

open Set
open Filter
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresBR

noncomputable def supportSuffixNumeral (A : Set ℕ) [DecidablePred (· ∈ A)]
    (M : ℕ) : ℕ → ℕ
  | 0 => 0
  | L + 1 =>
      2 * supportSuffixNumeral A M L +
        if M + L + 1 ∈ A then 1 else 0

noncomputable def EvenSeamReachable (δ c k : ℤ) : Prop :=
  (∃ h : ℤ, h ≤ δ ∧ (k = 2 * h - c - 1 ∨ k = 2 * h - c - 2)) ∨
  (∃ h : ℤ, δ < h ∧ (k = 2 * h - c ∨ k = 2 * h - c - 1))

noncomputable def halfStripBound (n : ℕ) : ℕ :=
  2 * Nat.sqrt n + 4

noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1

noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool

noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}

noncomputable def HalfStripAdmissible (N : ℕ) (a : HalfWord N) : Prop :=
  a ⟨0, Nat.zero_lt_succ N⟩ = false ∧
  (∀ h : 1 < N + 1, a ⟨1, h⟩ = false) ∧
  ∀ n : ℕ, 1 ≤ n → n ≤ N →
    (1 : ℤ) ≤ integerHalfCarry (wordSupport a) (n - 1) ∧
      integerHalfCarry (wordSupport a) (n - 1) ≤ halfStripBound n

noncomputable def restrictWord {M N : ℕ} (hMN : M ≤ N) (a : HalfWord N) : HalfWord M :=
  fun i ↦ a ⟨i, lt_of_lt_of_le i.isLt (Nat.succ_le_succ hMN)⟩

structure SelectedHalfWindow (N R : ℕ) where
  word : ∀ k : ℕ, 1 ≤ k → k ≤ R → HalfWord N
  admissible : ∀ k hk hkR, HalfStripAdmissible N (word k hk hkR)
  terminal : ∀ k hk hkR,
    integerHalfCarry (wordSupport (word k hk hkR)) (N - 1) = k

noncomputable def extendHalfWord {N : ℕ} (a : HalfWord N) (β : Bool) : HalfWord (N + 1) :=
  Fin.lastCases β a

noncomputable def wordSuffixNumeral
    {N : ℕ} (a : HalfWord N) (M L : ℕ) : ℕ :=
  @supportSuffixNumeral (wordSupport a) (Classical.decPred _) M L

noncomputable def HasSuffixCylinderAt
    {M N R : ℕ} (W : SelectedHalfWindow N R) (hMN : M ≤ N)
    (endpoint : ℕ) : Prop :=
  ∃ pfx : HalfWord M,
    ∀ k (hk : 1 ≤ k) (hkR : k ≤ R),
      restrictWord hMN (W.word k hk hkR) = pfx ∧
        wordSuffixNumeral (W.word k hk hkR) M (N - M) + k =
          endpoint

structure SelectedHalfInterval (N L U : ℕ) where
  word : ∀ q : ℕ, L ≤ q → q ≤ U → HalfWord N
  admissible : ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
    HalfStripAdmissible N (word q hqL hqU)
  terminal : ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
    integerHalfCarry (wordSupport (word q hqL hqU)) (N - 1) = q

noncomputable def HasSuffixCylinderOnInterval
    {M N L U : ℕ} (W : SelectedHalfInterval N L U)
    (hMN : M ≤ N) (endpoint : ℕ) : Prop :=
  ∃ pfx : HalfWord M,
    ∀ q (hqL : L ≤ q) (hqU : q ≤ U),
      restrictWord hMN (W.word q hqL hqU) = pfx ∧
        wordSuffixNumeral (W.word q hqL hqU) M (N - M) + q = endpoint

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

structure CylinderStage (K N : ℕ) where
  hKN : K ≤ N
  window : SelectedHalfWindow N (halfStripBound N)
  endpoint : ℕ
  cylinder : HasSuffixCylinderAt window hKN endpoint
  covers : halfStripBound N ≤ endpoint

/-- States the paper statement it is bound to from the long record for Erdős problem #257.
Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_feedback_row_total_dichotomy
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem paper_feedback_row_total_dichotomy
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    Nonempty (CylinderStage (K + 1) (N + 1)) ∨
      Nonempty (InStripTwoSheetStage K (N + 1)) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresBR
