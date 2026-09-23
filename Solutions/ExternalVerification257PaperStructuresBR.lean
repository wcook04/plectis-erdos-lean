/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CertificateKernel
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCarryRewindPhase
import Erdos249257.HalfCarrySelectedWindow
import Erdos249257.SelectedSuffixCylinder
import Erdos249257.SuffixCylinderInStrip
import Erdos249257.SuffixCylinderThreshold
import ErdosProblems.Erdos257.PaperCompleteR21.FeedbackRowStripWitnessAllDepths

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

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied structure `SelectedHalfWindow` and its source `Erdos249257.HalfCarrySelectedWindow.SelectedHalfWindow` carry the same
fields, so each converts into the other field by field. -/
noncomputable def SelectedHalfWindow_transport_toSrc {N R : ℕ} (x : SelectedHalfWindow N R) :
    Erdos249257.HalfCarrySelectedWindow.SelectedHalfWindow N R :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.word), (by set_option smartUnfolding false in with_unfolding_all exact x.admissible), (by set_option smartUnfolding false in with_unfolding_all exact x.terminal)⟩

/-- The inverse of `SelectedHalfWindow_transport_toSrc`. -/
noncomputable def SelectedHalfWindow_transport_ofSrc {N R : ℕ} (x : Erdos249257.HalfCarrySelectedWindow.SelectedHalfWindow N R) :
    SelectedHalfWindow N R :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.word), (by set_option smartUnfolding false in with_unfolding_all exact x.admissible), (by set_option smartUnfolding false in with_unfolding_all exact x.terminal)⟩

/-- The copied structure `SelectedHalfInterval` and its source `Erdos249257.SuffixCylinderInStrip.SelectedHalfInterval` carry the same
fields, so each converts into the other field by field. -/
noncomputable def SelectedHalfInterval_transport_toSrc {N L U : ℕ} (x : SelectedHalfInterval N L U) :
    Erdos249257.SuffixCylinderInStrip.SelectedHalfInterval N L U :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.word), (by set_option smartUnfolding false in with_unfolding_all exact x.admissible), (by set_option smartUnfolding false in with_unfolding_all exact x.terminal)⟩

/-- The inverse of `SelectedHalfInterval_transport_toSrc`. -/
noncomputable def SelectedHalfInterval_transport_ofSrc {N L U : ℕ} (x : Erdos249257.SuffixCylinderInStrip.SelectedHalfInterval N L U) :
    SelectedHalfInterval N L U :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.word), (by set_option smartUnfolding false in with_unfolding_all exact x.admissible), (by set_option smartUnfolding false in with_unfolding_all exact x.terminal)⟩

/-- The copied structure `InStripTwoSheetStage` and its source `Erdos249257.SuffixCylinderInStrip.InStripTwoSheetStage` carry the same
fields, so each converts into the other field by field. -/
noncomputable def InStripTwoSheetStage_transport_toSrc {K N : ℕ} (x : InStripTwoSheetStage K N) :
    Erdos249257.SuffixCylinderInStrip.InStripTwoSheetStage K N :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.hK1N), x.hole, (by set_option smartUnfolding false in with_unfolding_all exact x.hole_pos), (by set_option smartUnfolding false in with_unfolding_all exact x.hole_le), (by set_option smartUnfolding false in with_unfolding_all exact x.boundaryPrefix), (SelectedHalfWindow_transport_toSrc x.lower), (by set_option smartUnfolding false in with_unfolding_all exact x.lowerCylinder), (by set_option smartUnfolding false in with_unfolding_all exact x.lowerLiteral), x.upperEndpoint, (SelectedHalfInterval_transport_toSrc x.upper), (by set_option smartUnfolding false in with_unfolding_all exact x.upperCylinder), (by set_option smartUnfolding false in with_unfolding_all exact x.upperLiteral), (by set_option smartUnfolding false in with_unfolding_all exact x.upperCovers), (by set_option smartUnfolding false in with_unfolding_all exact x.endpointSeparation), x.seamCut, x.seamCoeff, (by set_option smartUnfolding false in with_unfolding_all exact x.hole_eq), (by set_option smartUnfolding false in with_unfolding_all exact x.scalar_exact)⟩

/-- The inverse of `InStripTwoSheetStage_transport_toSrc`. -/
noncomputable def InStripTwoSheetStage_transport_ofSrc {K N : ℕ} (x : Erdos249257.SuffixCylinderInStrip.InStripTwoSheetStage K N) :
    InStripTwoSheetStage K N :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.hK1N), x.hole, (by set_option smartUnfolding false in with_unfolding_all exact x.hole_pos), (by set_option smartUnfolding false in with_unfolding_all exact x.hole_le), (by set_option smartUnfolding false in with_unfolding_all exact x.boundaryPrefix), (SelectedHalfWindow_transport_ofSrc x.lower), (by set_option smartUnfolding false in with_unfolding_all exact x.lowerCylinder), (by set_option smartUnfolding false in with_unfolding_all exact x.lowerLiteral), x.upperEndpoint, (SelectedHalfInterval_transport_ofSrc x.upper), (by set_option smartUnfolding false in with_unfolding_all exact x.upperCylinder), (by set_option smartUnfolding false in with_unfolding_all exact x.upperLiteral), (by set_option smartUnfolding false in with_unfolding_all exact x.upperCovers), (by set_option smartUnfolding false in with_unfolding_all exact x.endpointSeparation), x.seamCut, x.seamCoeff, (by set_option smartUnfolding false in with_unfolding_all exact x.hole_eq), (by set_option smartUnfolding false in with_unfolding_all exact x.scalar_exact)⟩

@[simp] theorem InStripTwoSheetStage_transport_toSrc_hole {K N : ℕ}
    (x : InStripTwoSheetStage K N) :
    (InStripTwoSheetStage_transport_toSrc x).hole = x.hole := rfl

@[simp] theorem InStripTwoSheetStage_transport_ofSrc_hole {K N : ℕ}
    (x : Erdos249257.SuffixCylinderInStrip.InStripTwoSheetStage K N) :
    (InStripTwoSheetStage_transport_ofSrc x).hole = x.hole := rfl

@[simp] theorem InStripTwoSheetStage_transport_toSrc_upperEndpoint {K N : ℕ}
    (x : InStripTwoSheetStage K N) :
    (InStripTwoSheetStage_transport_toSrc x).upperEndpoint = x.upperEndpoint := rfl

@[simp] theorem InStripTwoSheetStage_transport_ofSrc_upperEndpoint {K N : ℕ}
    (x : Erdos249257.SuffixCylinderInStrip.InStripTwoSheetStage K N) :
    (InStripTwoSheetStage_transport_ofSrc x).upperEndpoint = x.upperEndpoint := rfl

@[simp] theorem InStripTwoSheetStage_transport_toSrc_seamCut {K N : ℕ}
    (x : InStripTwoSheetStage K N) :
    (InStripTwoSheetStage_transport_toSrc x).seamCut = x.seamCut := rfl

@[simp] theorem InStripTwoSheetStage_transport_ofSrc_seamCut {K N : ℕ}
    (x : Erdos249257.SuffixCylinderInStrip.InStripTwoSheetStage K N) :
    (InStripTwoSheetStage_transport_ofSrc x).seamCut = x.seamCut := rfl

@[simp] theorem InStripTwoSheetStage_transport_toSrc_seamCoeff {K N : ℕ}
    (x : InStripTwoSheetStage K N) :
    (InStripTwoSheetStage_transport_toSrc x).seamCoeff = x.seamCoeff := rfl

@[simp] theorem InStripTwoSheetStage_transport_ofSrc_seamCoeff {K N : ℕ}
    (x : Erdos249257.SuffixCylinderInStrip.InStripTwoSheetStage K N) :
    (InStripTwoSheetStage_transport_ofSrc x).seamCoeff = x.seamCoeff := rfl

/-- The copied structure `InStripTwoSheetStage` is inhabited exactly when its source is. -/
theorem InStripTwoSheetStage_transport_nonempty {K N : ℕ} :
    Nonempty (InStripTwoSheetStage K N) ↔ Nonempty (Erdos249257.SuffixCylinderInStrip.InStripTwoSheetStage K N) :=
  ⟨fun ⟨x⟩ => ⟨InStripTwoSheetStage_transport_toSrc x⟩,
    fun ⟨x⟩ => ⟨InStripTwoSheetStage_transport_ofSrc x⟩⟩

/-- The copied structure `CylinderStage` and its source `Erdos249257.SuffixCylinderThreshold.CylinderStage` carry the same
fields, so each converts into the other field by field. -/
noncomputable def CylinderStage_transport_toSrc {K N : ℕ} (x : CylinderStage K N) :
    Erdos249257.SuffixCylinderThreshold.CylinderStage K N :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.hKN), (SelectedHalfWindow_transport_toSrc x.window), x.endpoint, (by set_option smartUnfolding false in with_unfolding_all exact x.cylinder), (by set_option smartUnfolding false in with_unfolding_all exact x.covers)⟩

/-- The inverse of `CylinderStage_transport_toSrc`. -/
noncomputable def CylinderStage_transport_ofSrc {K N : ℕ} (x : Erdos249257.SuffixCylinderThreshold.CylinderStage K N) :
    CylinderStage K N :=
  ⟨(by set_option smartUnfolding false in with_unfolding_all exact x.hKN), (SelectedHalfWindow_transport_ofSrc x.window), x.endpoint, (by set_option smartUnfolding false in with_unfolding_all exact x.cylinder), (by set_option smartUnfolding false in with_unfolding_all exact x.covers)⟩

@[simp] theorem CylinderStage_transport_toSrc_endpoint {K N : ℕ}
    (x : CylinderStage K N) :
    (CylinderStage_transport_toSrc x).endpoint = x.endpoint := rfl

@[simp] theorem CylinderStage_transport_ofSrc_endpoint {K N : ℕ}
    (x : Erdos249257.SuffixCylinderThreshold.CylinderStage K N) :
    (CylinderStage_transport_ofSrc x).endpoint = x.endpoint := rfl

/-- The copied structure `CylinderStage` is inhabited exactly when its source is. -/
theorem CylinderStage_transport_nonempty {K N : ℕ} :
    Nonempty (CylinderStage K N) ↔ Nonempty (Erdos249257.SuffixCylinderThreshold.CylinderStage K N) :=
  ⟨fun ⟨x⟩ => ⟨CylinderStage_transport_toSrc x⟩,
    fun ⟨x⟩ => ⟨CylinderStage_transport_ofSrc x⟩⟩

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral` is the same function. -/
theorem supportSuffixNumeral_transport_def : @supportSuffixNumeral = @Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral := by
  first
  | (rfl; done)
  | (simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (with_unfolding_all rfl; done)
  | (unfold supportSuffixNumeral Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral; done)
  | (unfold supportSuffixNumeral Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (ext x; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a; fun_induction supportSuffixNumeral a <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a; induction a <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a; induction a <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a; induction a <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a; simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a b; fun_induction supportSuffixNumeral a b <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction b <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction a generalizing b <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; induction b generalizing a <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b; simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (funext a b c; fun_induction supportSuffixNumeral a b c <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction c <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext a b c; simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (simp [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral] <;> rfl; done)
  | (funext v1 v2; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral] <;> rfl; done)
  | (funext v1 v2 v3; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral] <;> rfl; done)
  | (funext v1 v2 v3 v4; simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral] <;> rfl; done)
  | (funext v1 v2 v3 v4; fun_induction supportSuffixNumeral v1 v2 v3 v4 <;> simp only [Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext v1 v2 v3 v4; induction v1 generalizing v2 v3 v4 <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext v1 v2 v3 v4; induction v2 generalizing v1 v3 v4 <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext v1 v2 v3 v4; induction v3 generalizing v1 v2 v4 <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)
  | (funext v1 v2 v3 v4; induction v4 generalizing v1 v2 v3 <;> simp only [supportSuffixNumeral, Erdos249257.FixedCoeffRewindPhase.supportSuffixNumeral, *]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.affineBinaryOrbit` is the same function. -/
theorem affineBinaryOrbit_transport_def : @affineBinaryOrbit = @Erdos249257.affineBinaryOrbit := by
  first
  | (rfl; done)
  | (simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit <;> simp only [Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (ext x; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a; fun_induction affineBinaryOrbit a <;> simp only [Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a b; fun_induction affineBinaryOrbit a b <;> simp only [Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (funext a b c; fun_induction affineBinaryOrbit a b c <;> simp only [Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def, *]; done)
  | (funext a b c; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)
  | (simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, supportSuffixNumeral_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCarryReachability.integerHalfCarry` is the same function. -/
theorem integerHalfCarry_transport_def : @integerHalfCarry = @Erdos249257.HalfCarryReachability.integerHalfCarry := by
  first
  | (rfl; done)
  | (simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry; done)
  | (unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (ext x; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a; fun_induction integerHalfCarry a <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a b; fun_induction integerHalfCarry a b <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (funext a b c; fun_induction integerHalfCarry a b c <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1; unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCarryReachability.HalfStripAdmissible` is the same function. -/
theorem HalfStripAdmissible_transport_def : @HalfStripAdmissible = @Erdos249257.HalfCarryReachability.HalfStripAdmissible := by
  first
  | (rfl; done)
  | (simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold HalfStripAdmissible Erdos249257.HalfCarryReachability.HalfStripAdmissible; done)
  | (unfold HalfStripAdmissible Erdos249257.HalfCarryReachability.HalfStripAdmissible <;> simp only [Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (ext x; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a; fun_induction HalfStripAdmissible a <;> simp only [Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b; fun_induction HalfStripAdmissible a b <;> simp only [Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b c; fun_induction HalfStripAdmissible a b c <;> simp only [Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (simp [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def] <;> rfl; done)
  | (funext v1; unfold HalfStripAdmissible Erdos249257.HalfCarryReachability.HalfStripAdmissible <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [HalfStripAdmissible, Erdos249257.HalfCarryReachability.HalfStripAdmissible, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold HalfStripAdmissible Erdos249257.HalfCarryReachability.HalfStripAdmissible <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral` is the same function. -/
theorem wordSuffixNumeral_transport_def : @wordSuffixNumeral = @Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral := by
  first
  | (rfl; done)
  | (simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral; done)
  | (unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (ext x; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a; fun_induction wordSuffixNumeral a <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a; induction a <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a; induction a <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a; induction a <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a; simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a b; fun_induction wordSuffixNumeral a b <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b; simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (funext a b c; fun_induction wordSuffixNumeral a b c <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext a b c; simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (simp [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1; unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3 v4; simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3 v4; unfold wordSuffixNumeral Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def] <;> rfl; done)
  | (funext v1 v2 v3 v4; fun_induction wordSuffixNumeral v1 v2 v3 v4 <;> simp only [Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext v1 v2 v3 v4; induction v1 generalizing v2 v3 v4 <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext v1 v2 v3 v4; induction v2 generalizing v1 v3 v4 <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext v1 v2 v3 v4; induction v3 generalizing v1 v2 v4 <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)
  | (funext v1 v2 v3 v4; induction v4 generalizing v1 v2 v3 <;> simp only [wordSuffixNumeral, Erdos249257.SelectedSuffixCylinder.wordSuffixNumeral, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, *]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt`, read through the structure maps, is the source. -/
@[simp] theorem HasSuffixCylinderAt_transport_def {M N R : ℕ} (W : SelectedHalfWindow N R) (hMN : M ≤ N) (endpoint : ℕ) :
    @Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt M N R (SelectedHalfWindow_transport_toSrc W) hMN endpoint = @HasSuffixCylinderAt M N R W hMN endpoint := by
  first
  | (rfl; done)
  | (simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> simp only [Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (ext x; simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a; fun_induction HasSuffixCylinderAt a <;> simp only [Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a; induction a <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a; simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a b; fun_induction HasSuffixCylinderAt a b <;> simp only [Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b; simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (funext a b c; fun_induction HasSuffixCylinderAt a b c <;> simp only [Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, *]; done)
  | (funext a b c; simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (simp [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> with_unfolding_all rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def] <;> rfl; done)
  | (simp only [HasSuffixCylinderAt, Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def] <;> rfl; done)
  | (unfold HasSuffixCylinderAt Erdos249257.SelectedSuffixCylinder.HasSuffixCylinderAt <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def] <;> set_option smartUnfolding false in with_unfolding_all rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval`, read through the structure maps, is the source. -/
@[simp] theorem HasSuffixCylinderOnInterval_transport_def {M N L U : ℕ} (W : SelectedHalfInterval N L U) (hMN : M ≤ N) (endpoint : ℕ) :
    @Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval M N L U (SelectedHalfInterval_transport_toSrc W) hMN endpoint = @HasSuffixCylinderOnInterval M N L U W hMN endpoint := by
  first
  | (rfl; done)
  | (simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold HasSuffixCylinderOnInterval Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval; done)
  | (unfold HasSuffixCylinderOnInterval Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval <;> simp only [Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (ext x; simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def]; done)
  | (funext a; fun_induction HasSuffixCylinderOnInterval a <;> simp only [Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a; induction a <;> simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a; induction a <;> simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a; simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def]; done)
  | (funext a b; fun_induction HasSuffixCylinderOnInterval a b <;> simp only [Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b; simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def]; done)
  | (funext a b c; fun_induction HasSuffixCylinderOnInterval a b c <;> simp only [Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, *]; done)
  | (funext a b c; simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def]; done)
  | (simp [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (unfold HasSuffixCylinderOnInterval Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval <;> rfl; done)
  | (unfold HasSuffixCylinderOnInterval Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval <;> with_unfolding_all rfl; done)
  | (unfold HasSuffixCylinderOnInterval Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def] <;> rfl; done)
  | (simp only [HasSuffixCylinderOnInterval, Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def] <;> rfl; done)
  | (unfold HasSuffixCylinderOnInterval Erdos249257.SuffixCylinderInStrip.HasSuffixCylinderOnInterval <;> simp only [supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def] <;> set_option smartUnfolding false in with_unfolding_all rfl; done)

theorem paper_feedback_row_total_dichotomy
    {K N : ℕ} (S : CylinderStage K N) (hK1N : K + 1 ≤ N)
    (hrow : N + 1 = 2 * (K + 1)) :
    Nonempty (CylinderStage (K + 1) (N + 1)) ∨
      Nonempty (InStripTwoSheetStage K (N + 1)) := by
  simpa only [CylinderStage_transport_toSrc_endpoint, InStripTwoSheetStage_transport_toSrc_hole, InStripTwoSheetStage_transport_toSrc_seamCoeff, InStripTwoSheetStage_transport_toSrc_seamCut, InStripTwoSheetStage_transport_toSrc_upperEndpoint, supportSuffixNumeral_transport_def, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, HalfStripAdmissible_transport_def, wordSuffixNumeral_transport_def, HasSuffixCylinderAt_transport_def, HasSuffixCylinderOnInterval_transport_def, InStripTwoSheetStage_transport_nonempty, CylinderStage_transport_nonempty] using @ErdosProblems.Erdos257.PaperCompleteR21.paper_feedback_row_total_dichotomy K N (CylinderStage_transport_toSrc S) hK1N hrow

end Erdos249257.ExternalVerification257PaperStructuresBR
