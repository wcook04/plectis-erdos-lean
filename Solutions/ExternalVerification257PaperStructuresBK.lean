/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CertificateKernel
import Erdos249257.DyadicPrefixCompression
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.GreedyAchievementSet
import Erdos249257.HalfCarryReachability
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderFiniteShadow
import Erdos249257.HalfCylinderFullShellSeamBridge
import Erdos249257.HalfCylinderHalfMembershipClassification
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.ResetSqrtEscapeHalfMembership
import ErdosProblems.Erdos257.PaperCompleteR21.SeamEscapeAndTerminalStrip

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a declaration of the substantive development in this repository,
at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos: a refereed paper statement, or a lemma or a proof
field that a copied definition names, as its documentation says. The definitions are local
copies of the source definitions, so the statements elaborate against Mathlib alone. This
module is a comparison interface over that development, not the development itself. The
mathematics is developed in
`Erdos249257.CertificateKernel`, `Erdos249257.DyadicPrefixCompression`,
`Erdos249257.GenericTailOrbitRigidity`, `Erdos249257.GreedyAchievementSet`,
`Erdos249257.HalfCarryReachability`, `Erdos249257.HalfCylinderConcreteSeamAdapter`,
`Erdos249257.HalfCylinderFiniteShadow`, `Erdos249257.HalfCylinderFullShellSeamBridge`,
`Erdos249257.HalfCylinderHalfMembershipClassification`,
`Erdos249257.HalfCylinderIntegerGreedy`,
`ErdosProblems.Erdos257.PaperCompleteR21.ResetSqrtEscapeHalfMembership`,
`ErdosProblems.Erdos257.PaperCompleteR21.SeamEscapeAndTerminalStrip`.
-/

open scoped BigOperators
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

namespace Erdos249257.ExternalVerification257PaperStructuresBK

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

noncomputable def mobiusCenteredHalfCarry (A : Set ℕ) (N : ℕ) : ℤ :=
  integerHalfCarry A N - 1

noncomputable def finiteCoeffWindowNumerator
    (A : Set ℕ) (n : ℕ) : ℕ → ℕ
  | 0 => 0
  | J + 1 =>
      2 * finiteCoeffWindowNumerator A n J +
        supportCoeff A (n + J + 1)

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

structure PerturbedFamily.AdjacentCut {α : Type*} (F : PerturbedFamily α) (C : ℕ) where
  below : α
  above : α
  below_admissible : F.oldSum below ≤ C
  below_maximal : ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below
  above_strict : C < F.oldSum above
  above_minimal : ∀ x, C < F.oldSum x → F.oldSum above ≤ F.oldSum x

noncomputable def PerturbedFamily.AdjacentCut.abovePulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.above

noncomputable def PerturbedFamily.AdjacentCut.belowPulse {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.pulse K.below

noncomputable def PerturbedFamily.AdjacentCut.overshoot {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.oldSum K.above - C

noncomputable def PerturbedFamily.AdjacentCut.remainder {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := C - F.oldSum K.below

noncomputable def PerturbedFamily.AdjacentCut.successorCarries {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : Prop :=
  4 * K.overshoot + K.abovePulse ≤ F.gap

noncomputable def PerturbedFamily.AdjacentCut.terminalWeight {α : Type*} {F : PerturbedFamily α} {C : ℕ} (_K : F.AdjacentCut C) : ℕ := 2 * F.gap + 4

noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool

noncomputable def SeamRowWord.ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)

noncomputable def SeamRowWord.toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

noncomputable def wordWeightSum (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then truncatedMersenneWeight s (i + 2) else 0

theorem seamPerturbedFamily_gap_pos (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    0 < gap := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).gap_pos

theorem seamPerturbedFamily_oldSum_injective (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    Function.Injective oldSum := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).oldSum_injective

theorem seamPerturbedFamily_separated (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    let gap : ℕ := 2 ^ (s + 1);
    ∀ {x y}, oldSum x < oldSum y → oldSum x + gap ≤ oldSum y := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).separated

theorem seamPerturbedFamily_pulseCap_lt_three_gap (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    let pulseCap : ℕ := 2 * (s - 2);
    pulseCap < 3 * gap := (@Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily s hs).pulseCap_lt_three_gap

noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)

noncomputable def wordPulse (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then rowPulse s (i + 2) else 0

theorem wordPulse_le (s : ℕ) (b : ℕ → Bool) :
    wordPulse s b ≤ 2 * (s - 2) := @Erdos249257.HalfCylinderIntegerGreedy.wordPulse_le s b

noncomputable def seamPerturbedFamily (s : ℕ) (hs : 3 ≤ s) :
    PerturbedFamily (SeamRowWord s) where
  oldSum b := wordWeightSum s b.toNatWord
  pulse b := wordPulse s b.toNatWord
  gap := 2 ^ (s + 1)
  pulseCap := 2 * (s - 2)
  gap_pos := @seamPerturbedFamily_gap_pos s hs
  pulse_le b := wordPulse_le s b.toNatWord
  oldSum_injective := @seamPerturbedFamily_oldSum_injective s hs
  separated := @seamPerturbedFamily_separated s hs
  pulseCap_lt_three_gap := @seamPerturbedFamily_pulseCap_lt_three_gap s hs

noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

theorem exists_seamWord_minimal_above
    {s : ℕ} (hs : 5 ≤ s) :
    ∃ a : SeamRowWord s,
      seamSubsetTarget s <
          (seamPerturbedFamily s (by omega)).oldSum a ∧
        ∀ x : SeamRowWord s,
          seamSubsetTarget s <
              (seamPerturbedFamily s (by omega)).oldSum x →
            (seamPerturbedFamily s (by omega)).oldSum a ≤
              (seamPerturbedFamily s (by omega)).oldSum x := @Erdos249257.HalfCylinderIntegerGreedy.exists_seamWord_minimal_above s hs

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

theorem integerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (integerGreedyBits weights C).length = weights.length := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits_length weights C

noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0

noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

noncomputable def seamAboveWord (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord s :=
  Classical.choose (exists_seamWord_minimal_above hs)

theorem seamAboveWord_minimal
    {s : ℕ} (hs : 5 ≤ s) (x : SeamRowWord s)
    (hx : seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum x) :
    (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) ≤
      (seamPerturbedFamily s (by omega)).oldSum x := @Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_minimal s hs x hx

theorem seamAboveWord_strict
    {s : ℕ} (hs : 5 ≤ s) :
    seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) := @Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_strict s hs

noncomputable def seamWeightsFrom (s : ℕ) : ℕ → List ℕ
  | d =>
      if h : d < s then
        truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1)
      else
        []
termination_by d => s - d
decreasing_by omega

noncomputable def seamWeights (s : ℕ) : List ℕ :=
  seamWeightsFrom s 2

theorem seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  set_option smartUnfolding false in
  with_unfolding_all exact @Erdos249257.HalfCylinderIntegerGreedy.seamWeights_length_eq s

noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  SeamRowWord.ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])

theorem seamAdjacentCut_below_admissible (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    F.oldSum below ≤ C := by
  set_option smartUnfolding false in
  with_unfolding_all exact (@Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).below_admissible

theorem seamAdjacentCut_below_maximal (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below := by
  set_option smartUnfolding false in
  with_unfolding_all exact (@Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut s hs).below_maximal

noncomputable def seamAdjacentCut (s : ℕ) (hs : 5 ≤ s) :
    (seamPerturbedFamily s (by omega)).AdjacentCut
      (seamSubsetTarget s) where
  below := seamGreedyWord s
  above := seamAboveWord s hs
  below_admissible := @seamAdjacentCut_below_admissible s hs
  below_maximal := @seamAdjacentCut_below_maximal s hs
  above_strict := seamAboveWord_strict hs
  above_minimal := seamAboveWord_minimal hs

noncomputable def seamIntegerGreedyRemainder (s : ℕ) : ℕ :=
  integerGreedyRemainder (seamWeights s) (seamSubsetTarget s)

noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)

noncomputable def greedyMersenneRemainder (x : ℝ) : ℕ → ℝ
  | 0 => x
  | n + 1 =>
      if mersenneWeight (n + 1) ≤ greedyMersenneRemainder x n then
        greedyMersenneRemainder x n - mersenneWeight (n + 1)
      else
        greedyMersenneRemainder x n

noncomputable def mersenneWeightRat (n : ℕ) : ℚ :=
  1 / ((2 : ℚ) ^ n - 1)

noncomputable def greedyMersenneRemainderRat (x : ℚ) : ℕ → ℚ
  | 0 => x
  | n + 1 =>
      if mersenneWeightRat (n + 1) ≤ greedyMersenneRemainderRat x n then
        greedyMersenneRemainderRat x n - mersenneWeightRat (n + 1)
      else
        greedyMersenneRemainderRat x n

noncomputable def greedyMersennePrefixRat (x : ℚ) (n : ℕ) : Finset ℕ :=
  (((Finset.range n).filter fun k =>
      mersenneWeightRat (k + 1) ≤ greedyMersenneRemainderRat x k).image
    fun k => k + 1)

noncomputable def halfGreedyPrefixSupport (n : ℕ) : Finset ℕ :=
  greedyMersennePrefixRat (1 / 2 : ℚ) n

noncomputable def greedyHalfFrozenMargin (k J : ℕ) : ℤ :=
  (finiteCoeffWindowNumerator
      (↑(halfGreedyPrefixSupport k) : Set ℕ) (k + 1) J : ℤ) -
    (2 : ℤ) ^ J *
      mobiusCenteredHalfCarry
        (↑(halfGreedyPrefixSupport k) : Set ℕ) k

noncomputable def HalfGreedySkippedFullShellNonnegative : Prop :=
  ∀ n : ℕ, 3 ≤ n →
    (¬ mersenneWeight n ≤
      greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
    0 ≤ greedyHalfFrozenMargin (n - 1) n

noncomputable def SeamGreedyUpperOrMiddleAt (s : ℕ) (hs : 5 ≤ s) : Prop :=
  (seamAdjacentCut s hs).successorCarries ∨
    (¬ (seamAdjacentCut s hs).successorCarries ∧
      4 * (seamAdjacentCut s hs).remainder +
            (seamPerturbedFamily s (by omega)).gap -
            (seamAdjacentCut s hs).belowPulse <
        (seamAdjacentCut s hs).terminalWeight)

noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)

noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}

noncomputable def seamResetDeviation (r : ℕ) : ℤ :=
  (seamIntegerGreedyRemainder (r + 1) : ℤ) -
    ((2 ^ (r + 1) : ℕ) : ℤ)

noncomputable def SeamResetSqrtEscape : Prop :=
  ∀ (r : ℕ) (hr5 : 5 ≤ r), 10 ≤ r →
    SeamGreedyUpperOrMiddleAt r hr5 →
      ((2 ^ (r + 5) : ℕ) : ℤ) < seamResetDeviation r ^ 2

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The copied structure `PerturbedFamily` and its source `Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily` carry the same
fields, so each converts into the other field by field. -/
def PerturbedFamily_transport_toSrc {α : Type*} (x : PerturbedFamily α) :
    Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α :=
  ⟨x.oldSum, x.pulse, x.gap, x.pulseCap, x.gap_pos, x.pulse_le, x.oldSum_injective, x.separated, x.pulseCap_lt_three_gap⟩

/-- The inverse of `PerturbedFamily_transport_toSrc`. -/
def PerturbedFamily_transport_ofSrc {α : Type*} (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    PerturbedFamily α :=
  ⟨x.oldSum, x.pulse, x.gap, x.pulseCap, x.gap_pos, x.pulse_le, x.oldSum_injective, x.separated, x.pulseCap_lt_three_gap⟩

@[simp] theorem PerturbedFamily_transport_toSrc_oldSum {α : Type*}
    (x : PerturbedFamily α) :
    (PerturbedFamily_transport_toSrc x).oldSum = x.oldSum := rfl

@[simp] theorem PerturbedFamily_transport_ofSrc_oldSum {α : Type*}
    (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    (PerturbedFamily_transport_ofSrc x).oldSum = x.oldSum := rfl

@[simp] theorem PerturbedFamily_transport_toSrc_pulse {α : Type*}
    (x : PerturbedFamily α) :
    (PerturbedFamily_transport_toSrc x).pulse = x.pulse := rfl

@[simp] theorem PerturbedFamily_transport_ofSrc_pulse {α : Type*}
    (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    (PerturbedFamily_transport_ofSrc x).pulse = x.pulse := rfl

@[simp] theorem PerturbedFamily_transport_toSrc_gap {α : Type*}
    (x : PerturbedFamily α) :
    (PerturbedFamily_transport_toSrc x).gap = x.gap := rfl

@[simp] theorem PerturbedFamily_transport_ofSrc_gap {α : Type*}
    (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    (PerturbedFamily_transport_ofSrc x).gap = x.gap := rfl

@[simp] theorem PerturbedFamily_transport_toSrc_pulseCap {α : Type*}
    (x : PerturbedFamily α) :
    (PerturbedFamily_transport_toSrc x).pulseCap = x.pulseCap := rfl

@[simp] theorem PerturbedFamily_transport_ofSrc_pulseCap {α : Type*}
    (x : Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily α) :
    (PerturbedFamily_transport_ofSrc x).pulseCap = x.pulseCap := rfl

/-- The copied structure `PerturbedFamily.AdjacentCut` and its source `Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut` carry the same
fields, so each converts into the other field by field. -/
def PerturbedFamily.AdjacentCut_transport_toSrc {α : Type*} {F : PerturbedFamily α} {C : ℕ} (x : @PerturbedFamily.AdjacentCut α F C) :
    @Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut α (PerturbedFamily_transport_toSrc F) C :=
  ⟨x.below, x.above, x.below_admissible, x.below_maximal, x.above_strict, x.above_minimal⟩

/-- The inverse of `PerturbedFamily.AdjacentCut_transport_toSrc`. -/
def PerturbedFamily.AdjacentCut_transport_ofSrc {α : Type*} {F : PerturbedFamily α} {C : ℕ} (x : @Erdos249257.HalfCylinderIntegerGreedy.PerturbedFamily.AdjacentCut α (PerturbedFamily_transport_toSrc F) C) :
    @PerturbedFamily.AdjacentCut α F C :=
  ⟨x.below, x.above, x.below_admissible, x.below_maximal, x.above_strict, x.above_minimal⟩

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.affineBinaryOrbit` is the same function. -/
theorem affineBinaryOrbit_transport_def : @affineBinaryOrbit = @Erdos249257.affineBinaryOrbit := by
  first
  | (rfl; done)
  | (simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (with_unfolding_all rfl; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit; done)
  | (unfold affineBinaryOrbit Erdos249257.affineBinaryOrbit <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (ext x; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a; fun_induction affineBinaryOrbit a <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; induction a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; induction a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b; fun_induction affineBinaryOrbit a b <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction a generalizing b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; induction b generalizing a <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (funext a b c; fun_induction affineBinaryOrbit a b c <;> simp only [Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit, *]; done)
  | (funext a b c; simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)
  | (simp [affineBinaryOrbit, Erdos249257.affineBinaryOrbit]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCarryReachability.integerHalfCarry` is the same function. -/
theorem integerHalfCarry_transport_def : @integerHalfCarry = @Erdos249257.HalfCarryReachability.integerHalfCarry := by
  first
  | (rfl; done)
  | (simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry; done)
  | (unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (ext x; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a; fun_induction integerHalfCarry a <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a b; fun_induction integerHalfCarry a b <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (funext a b c; fun_induction integerHalfCarry a b c <;> simp only [Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def, *]; done)
  | (funext a b c; simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (simp [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1; unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [integerHalfCarry, Erdos249257.HalfCarryReachability.integerHalfCarry, affineBinaryOrbit_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold integerHalfCarry Erdos249257.HalfCarryReachability.integerHalfCarry <;> simp only [affineBinaryOrbit_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry` is the same function. -/
theorem mobiusCenteredHalfCarry_transport_def : @mobiusCenteredHalfCarry = @Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry := by
  first
  | (rfl; done)
  | (simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold mobiusCenteredHalfCarry Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry; done)
  | (unfold mobiusCenteredHalfCarry Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry <;> simp only [Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (ext x; simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a; fun_induction mobiusCenteredHalfCarry a <;> simp only [Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a; simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b; fun_induction mobiusCenteredHalfCarry a b <;> simp only [Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b; simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (funext a b c; fun_induction mobiusCenteredHalfCarry a b c <;> simp only [Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, *]; done)
  | (funext a b c; simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)
  | (simp [mobiusCenteredHalfCarry, Erdos249257.HalfCarryReachability.mobiusCenteredHalfCarry, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator` is the same function. -/
theorem finiteCoeffWindowNumerator_transport_def : @finiteCoeffWindowNumerator = @Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator := by
  first
  | (rfl; done)
  | (simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator; done)
  | (unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator <;> simp only [Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (ext x; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a; fun_induction finiteCoeffWindowNumerator a <;> simp only [Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a; induction a <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a; simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a b; fun_induction finiteCoeffWindowNumerator a b <;> simp only [Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b; simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (funext a b c; fun_induction finiteCoeffWindowNumerator a b c <;> simp only [Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def, *]; done)
  | (funext a b c; simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (simp [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1; unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator <;> simp only [affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator <;> simp only [affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; simp only [finiteCoeffWindowNumerator, Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator, affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; unfold finiteCoeffWindowNumerator Erdos249257.HalfCylinderFiniteShadow.finiteCoeffWindowNumerator <;> simp only [affineBinaryOrbit_transport_def, integerHalfCarry_transport_def, mobiusCenteredHalfCarry_transport_def] <;> rfl; done)


theorem half_mem_mersenneAchievementSet_of_resetSqrtEscape
    (hsqrt : SeamResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape hsqrt

theorem paper_seam_escape_forces_remainder_band
    {n : ℕ} (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    1 ≤ seamIntegerGreedyRemainder n ∧
      seamIntegerGreedyRemainder n ≤ halfStripBound (2 * n) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_forces_remainder_band n hn hskip hneg

theorem paper_seam_escape_implies_full_shell_nonnegative
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    HalfGreedySkippedFullShellNonnegative := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_full_shell_nonnegative hescape

end Erdos249257.ExternalVerification257PaperStructuresBK
