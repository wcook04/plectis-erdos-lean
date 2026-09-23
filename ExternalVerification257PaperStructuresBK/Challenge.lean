/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

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

/-- Proof obligation `gap_pos` of the local copy of
Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own
parameter and field values. The definition names this theorem for the field, and the
Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_gap_pos (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    0 < gap := by
  sorry

/-- Proof obligation `oldSum_injective` of the local copy of
Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own
parameter and field values. The definition names this theorem for the field, and the
Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_oldSum_injective (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    Function.Injective oldSum := by
  sorry

/-- Proof obligation `separated` of the local copy of
Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own
parameter and field values. The definition names this theorem for the field, and the
Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_separated (s : ℕ) (hs : 3 ≤ s) :
    let oldSum : (SeamRowWord s) → ℕ := fun b => wordWeightSum s b.toNatWord;
    let gap : ℕ := 2 ^ (s + 1);
    ∀ {x y}, oldSum x < oldSum y → oldSum x + gap ≤ oldSum y := by
  sorry

/-- Proof obligation `pulseCap_lt_three_gap` of the local copy of
Erdos249257.HalfCylinderIntegerGreedy.seamPerturbedFamily, stated with that definition's own
parameter and field values. The definition names this theorem for the field, and the
Solution proves it with the source definition's own field. -/
theorem seamPerturbedFamily_pulseCap_lt_three_gap (s : ℕ) (hs : 3 ≤ s) :
    let gap : ℕ := 2 ^ (s + 1);
    let pulseCap : ℕ := 2 * (s - 2);
    pulseCap < 3 * gap := by
  sorry

noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)

noncomputable def wordPulse (s : ℕ) (b : ℕ → Bool) : ℕ :=
  ∑ i ∈ Finset.range (s - 2),
    if b (i + 2) then rowPulse s (i + 2) else 0

/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.wordPulse_le, which a copied definition
cites. It is carried as a statement so that its proof stays in the source development, and
the Solution proves it by applying the source lemma. -/
theorem wordPulse_le (s : ℕ) (b : ℕ → Bool) :
    wordPulse s b ≤ 2 * (s - 2) := by
  sorry

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

/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.exists_seamWord_minimal_above, which a
copied definition cites. It is carried as a statement so that its proof stays in the source
development, and the Solution proves it by applying the source lemma. -/
theorem exists_seamWord_minimal_above
    {s : ℕ} (hs : 5 ≤ s) :
    ∃ a : SeamRowWord s,
      seamSubsetTarget s <
          (seamPerturbedFamily s (by omega)).oldSum a ∧
        ∀ x : SeamRowWord s,
          seamSubsetTarget s <
              (seamPerturbedFamily s (by omega)).oldSum x →
            (seamPerturbedFamily s (by omega)).oldSum a ≤
              (seamPerturbedFamily s (by omega)).oldSum x := by
  sorry

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits_length, which a copied
definition cites. It is carried as a statement so that its proof stays in the source
development, and the Solution proves it by applying the source lemma. -/
theorem integerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (integerGreedyBits weights C).length = weights.length := by
  sorry

noncomputable def weightedBoolSum : List ℕ → List Bool → ℕ
  | w :: ws, true :: bs => w + weightedBoolSum ws bs
  | _ :: ws, false :: bs => weightedBoolSum ws bs
  | _, _ => 0

noncomputable def integerGreedyRemainder (weights : List ℕ) (C : ℕ) : ℕ :=
  C - weightedBoolSum weights (integerGreedyBits weights C)

noncomputable def seamAboveWord (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord s :=
  Classical.choose (exists_seamWord_minimal_above hs)

/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_minimal, which a copied
definition cites. It is carried as a statement so that its proof stays in the source
development, and the Solution proves it by applying the source lemma. -/
theorem seamAboveWord_minimal
    {s : ℕ} (hs : 5 ≤ s) (x : SeamRowWord s)
    (hx : seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum x) :
    (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) ≤
      (seamPerturbedFamily s (by omega)).oldSum x := by
  sorry

/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.seamAboveWord_strict, which a copied
definition cites. It is carried as a statement so that its proof stays in the source
development, and the Solution proves it by applying the source lemma. -/
theorem seamAboveWord_strict
    {s : ℕ} (hs : 5 ≤ s) :
    seamSubsetTarget s <
      (seamPerturbedFamily s (by omega)).oldSum (seamAboveWord s hs) := by
  sorry

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

/-- Statement of Erdos249257.HalfCylinderIntegerGreedy.seamWeights_length_eq, which a copied
definition cites. It is carried as a statement so that its proof stays in the source
development, and the Solution proves it by applying the source lemma. -/
theorem seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  sorry

noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  SeamRowWord.ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])

/-- Proof obligation `below_admissible` of the local copy of
Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut, stated with that definition's own
parameter and field values. The definition names this theorem for the field, and the
Solution proves it with the source definition's own field. -/
theorem seamAdjacentCut_below_admissible (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    F.oldSum below ≤ C := by
  sorry

/-- Proof obligation `below_maximal` of the local copy of
Erdos249257.HalfCylinderIntegerGreedy.seamAdjacentCut, stated with that definition's own
parameter and field values. The definition names this theorem for the field, and the
Solution proves it with the source definition's own field. -/
theorem seamAdjacentCut_below_maximal (s : ℕ) (hs : 5 ≤ s) :
    let F := (seamPerturbedFamily s (by omega));
    let C := (seamSubsetTarget s);
    let below := seamGreedyWord s;
    ∀ x, F.oldSum x ≤ C → F.oldSum x ≤ F.oldSum below := by
  sorry

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

/-- States the paper statement it is bound to from the long record for Erdős problem #257.
Transported from
ErdosProblems.Erdos257.PaperCompleteR21.half_mem_mersenneAchievementSet_of_resetSqrtEscape
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem half_mem_mersenneAchievementSet_of_resetSqrtEscape
    (hsqrt : SeamResetSqrtEscape) :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet := by
  sorry

/-- States record:257bm-c15 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_forces_remainder_band in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_seam_escape_forces_remainder_band
    {n : ℕ} (hn : 3 ≤ n)
    (hskip : ¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1))
    (hneg : greedyHalfFrozenMargin (n - 1) n < 0) :
    1 ≤ seamIntegerGreedyRemainder n ∧
      seamIntegerGreedyRemainder n ≤ halfStripBound (2 * n) := by
  sorry

/-- States record:257bm-c15 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_seam_escape_implies_full_shell_nonnegative in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_seam_escape_implies_full_shell_nonnegative
    (hescape : ∀ n : ℕ, 3 ≤ n →
      (¬ mersenneWeight n ≤ greedyMersenneRemainder (1 / 2 : ℝ) (n - 1)) →
      halfStripBound (2 * n) < seamIntegerGreedyRemainder n) :
    HalfGreedySkippedFullShellNonnegative := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresBK
