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
`Erdos249257.HalfCylinderConcreteSeamAdapter`, `Erdos249257.HalfCylinderIntegerGreedy`,
`Erdos249257.HalfCylinderMiddleCarryLowerBound`, `Erdos249257.HalfUpperResetCriticalBand`,
`ErdosProblems.Erdos257.PaperCompleteR21.CriticalDyadicBandCollapse`.
-/

open Finset
open scoped BigOperators
open Set
open Filter

namespace Erdos249257.ExternalVerification257PaperStructuresBZ

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

noncomputable def PerturbedFamily.AdjacentCut.overshoot {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : ℕ := F.oldSum K.above - C

noncomputable def PerturbedFamily.AdjacentCut.successorCarries {α : Type*} {F : PerturbedFamily α} {C : ℕ} (K : F.AdjacentCut C) : Prop :=
  4 * K.overshoot + K.abovePulse ≤ F.gap

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

noncomputable def CriticalDyadicBandIndex (d E j : ℕ) : Prop :=
  j ≤ d ∧
    E ≤ 2 ^ (d - j + 1) ∧
      (j = d ∨ 2 ^ (d - (j + 1) + 1) < E)

noncomputable def DyadicBandEscape (d E : ℕ) : Prop :=
  ∀ j : ℕ, j ≤ d →
    2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)

noncomputable def seamUpperResetCharge (d : ℕ) (hd5 : 5 ≤ d) : ℕ :=
  4 * (seamAdjacentCut d hd5).overshoot +
    (seamAdjacentCut d hd5).abovePulse

noncomputable def SeamUpperResetCriticalBandEscape : Prop :=
  ∀ (d : ℕ) (hd5 : 5 ≤ d), 13 ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
      ∃ j : ℕ,
        CriticalDyadicBandIndex d (seamUpperResetCharge d hd5) j ∧
          seamUpperResetCharge d hd5 + 2 * (d + j) ≤
            2 ^ (d - j + 1)

noncomputable def SeamUpperResetDyadicBandEscape : Prop :=
  ∀ (d : ℕ) (hd5 : 5 ≤ d), 13 ≤ d →
    (seamAdjacentCut d hd5).successorCarries →
      ∀ j : ℕ, j ≤ d →
        2 ^ (d - j + 1) <
            4 * (seamAdjacentCut d hd5).overshoot +
              (seamAdjacentCut d hd5).abovePulse ∨
          4 * (seamAdjacentCut d hd5).overshoot +
                (seamAdjacentCut d hd5).abovePulse + 2 * (d + j) ≤
            2 ^ (d - j + 1)

/-- States thm:critical-dyadic-band from the long record for Erdős problem #257. Transported
from Erdos249257.HalfUpperResetCriticalBand.seamUpperResetCriticalBandEscape_iff in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem seamUpperResetCriticalBandEscape_iff :
    SeamUpperResetCriticalBandEscape ↔ SeamUpperResetDyadicBandEscape := by
  sorry

/-- States prop:critical-band-index from the long record for Erdős problem #257. Transported
from ErdosProblems.Erdos257.PaperCompleteR21.paper_critical_band_index_collapse in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_critical_band_index_collapse :
    (∀ d E : ℕ, DyadicBandEscape d E ↔
        ∀ j : ℕ, j ≤ d →
          2 ^ (d - j + 1) < E ∨ E + 2 * (d + j) ≤ 2 ^ (d - j + 1)) ∧
      (∀ d E : ℕ, E ≤ 2 ^ (d + 1) →
        (DyadicBandEscape d E ↔ ∃ j : ℕ, CriticalDyadicBandIndex d E j ∧
          E + 2 * (d + j) ≤ 2 ^ (d - j + 1))) ∧
      (∀ d E : ℕ, E ≤ 2 ^ (d + 1) → ∃ j : ℕ, CriticalDyadicBandIndex d E j) ∧
      (∀ d E : ℕ, 2 ^ (d + 1) < E → DyadicBandEscape d E) ∧
      (∀ d E : ℕ, 2 ^ (d + 1) < E → ¬ ∃ j : ℕ, CriticalDyadicBandIndex d E j) ∧
      (2 ^ (0 + 1) < 3 ∧ ∀ d E : ℕ, 2 ^ (d + 1) < E → 0 ≤ d ∧ 3 ≤ E) ∧
      (SeamUpperResetCriticalBandEscape ↔ SeamUpperResetDyadicBandEscape) := by
  sorry

end Erdos249257.ExternalVerification257PaperStructuresBZ
