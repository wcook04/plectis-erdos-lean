import ErdosProblems.Erdos257.MersenneSubseriesRigidity
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Measure.Comap
import Mathlib.MeasureTheory.Measure.Dirac
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Tactic

/-!
# Fair coding of the actual Mersenne achievement set

Recovered candidate source from the interrupted Type B authoring run.
Lean build and axiom audit UNRUN.
Coordinate `k : ℕ` is paper exponent `k + 1`.
-/
noncomputable section
namespace ErdosProblems.Erdos257.PaperGeometryCompletion

open Set MeasureTheory Topology
open Erdos257PeriodNoncollapse
open scoped ENNReal

abbrev Digits := ℕ → Fin 2

def pasteDigits (F : Finset ℕ) (b c : Digits) : Digits :=
  fun k => if k ∈ F then b k else c k

def digitCylinder (F : Finset ℕ) (b : Digits) : Set Digits :=
  {c | ∀ k ∈ F, c k = b k}

def finiteDigitValue (F : Finset ℕ) (b : Digits) : ℝ :=
  ∑ k ∈ F, mersenneDigitTerm k b

@[simp] theorem pasteDigits_empty (b c : Digits) : pasteDigits ∅ b c = c := by
  funext k; simp [pasteDigits]

@[simp] theorem finiteDigitValue_empty (b : Digits) : finiteDigitValue ∅ b = 0 := by
  simp [finiteDigitValue]

theorem value_pasteDigits (F : Finset ℕ) (b c : Digits)
    (hc : ∀ k ∈ F, c k = 0) :
    positiveMersenneDigitValue (pasteDigits F b c) =
      finiteDigitValue F b + positiveMersenneDigitValue c := by
  classical
  revert hc
  induction F using Finset.induction_on with
  | empty => intro _; simp
  | @insert k F hk ih =>
      intro hc
      have hcF : ∀ i ∈ F, c i = 0 := fun i hi => hc i (Finset.mem_insert_of_mem hi)
      have hck : c k = 0 := hc k (Finset.mem_insert_self _ _)
      have hp : pasteDigits (insert k F) b c = Function.update (pasteDigits F b c) k (b k) := by
        funext i
        by_cases hik : i = k
        · subst i; simp [pasteDigits]
        · simp [pasteDigits, Function.update, hik]
      rw [hp, positiveMersenneDigitValue_update]
      have hzero : pasteDigits F b c k = 0 := by simp [pasteDigits, hk, hck]
      rw [hzero, ih hcF]
      simp only [Fin.val_zero, Nat.cast_zero, sub_zero]
      simp only [finiteDigitValue, Finset.sum_insert hk, mersenneDigitTerm]
      ring

theorem isClosed_digitCylinder (F : Finset ℕ) (b : Digits) : IsClosed (digitCylinder F b) := by
  rw [show digitCylinder F b = ⋂ k ∈ (F : Set ℕ), {c : Digits | c k = b k} by
    ext c; simp [digitCylinder]]
  exact isClosed_biInter fun k _ => isClosed_eq (continuous_apply k) continuous_const

theorem measurableSet_digitCylinder (F : Finset ℕ) (b : Digits) :
    MeasurableSet (digitCylinder F b) := (isClosed_digitCylinder F b).measurableSet

theorem image_digitCylinder (F : Finset ℕ) (b : Digits) :
    positiveMersenneDigitValue '' digitCylinder F b =
      (fun x : ℝ => finiteDigitValue F b + x) ''
        supportedMersenneAchievementSet ((F : Set ℕ)ᶜ) := by
  classical
  ext x
  constructor
  · rintro ⟨c, hc, rfl⟩
    let z : Digits := pasteDigits F (fun _ => 0) c
    have hz : ∀ k ∈ F, z k = 0 := by intro k hk; simp [z, pasteDigits, hk]
    have hzS : ∀ k, k ∉ (F : Set ℕ)ᶜ → z k = 0 := by
      intro k hk; exact hz k (by simpa using hk)
    have hp : pasteDigits F b z = c := by
      funext k
      by_cases hk : k ∈ F
      · simp [pasteDigits, hk, (hc k hk).symm]
      · simp [pasteDigits, z, hk]
    refine ⟨positiveMersenneDigitValue z, ⟨⟨z, hzS⟩, rfl⟩, ?_⟩
    have hv := value_pasteDigits F b z hz
    rw [hp] at hv
    exact hv.symm
  · rintro ⟨_, ⟨z, rfl⟩, rfl⟩
    have hz : ∀ k ∈ F, z.1 k = 0 := by
      intro k hk; exact z.2 k (by simpa using hk)
    refine ⟨pasteDigits F b z.1, ?_, ?_⟩
    · intro k hk; simp [pasteDigits, hk]
    · exact value_pasteDigits F b z.1 hz

theorem volume_image_digitCylinder (F : Finset ℕ) (b : Digits) :
    volume (positiveMersenneDigitValue '' digitCylinder F b) =
      ((2 : ℝ≥0∞) ^ F.card)⁻¹ := by
  rw [image_digitCylinder, Set.image_add_left, measure_preimage_add]
  exact volume_supportedMersenneAchievementSet_finset_compl F

theorem measurableEmbedding_mersenneCoding : MeasurableEmbedding positiveMersenneDigitValue := by
  apply isEmbedding_positiveMersenneDigitValue.measurableEmbedding
  rw [range_positiveMersenneDigitValue_eq]
  exact isClosed_mersenneAchievementSet.measurableSet

def fairCoin : Measure (Fin 2) :=
  (2 : ℝ≥0∞)⁻¹ • Measure.dirac 0 + (2 : ℝ≥0∞)⁻¹ • Measure.dirac 1

instance fairCoin_isProbabilityMeasure : IsProbabilityMeasure fairCoin := by
  constructor
  norm_num [fairCoin]
  rw [← two_mul]
  exact ENNReal.mul_inv_cancel (by norm_num) (by norm_num)

@[simp] theorem fairCoin_singleton (a : Fin 2) : fairCoin {a} = (2 : ℝ≥0∞)⁻¹ := by
  fin_cases a <;> norm_num [fairCoin]

def fairDigits : Measure Digits := Measure.infinitePi (fun _ : ℕ => fairCoin)

instance fairDigits_isProbabilityMeasure : IsProbabilityMeasure fairDigits := by
  unfold fairDigits; infer_instance

theorem fairDigits_digitCylinder (F : Finset ℕ) (b : Digits) :
    fairDigits (digitCylinder F b) = ((2 : ℝ≥0∞) ^ F.card)⁻¹ := by
  have hset : digitCylinder F b = (F : Set ℕ).pi (fun k => {b k}) := by
    ext c; simp [digitCylinder]
  rw [fairDigits, hset, Measure.infinitePi_pi]
  · simp [ENNReal.inv_pow]
  · intro k _; exact measurableSet_singleton (b k)

def extendFiniteDigits (F : Finset ℕ) (u : F → Fin 2) : Digits :=
  fun k => if hk : k ∈ F then u ⟨k, hk⟩ else 0

theorem restrict_preimage_singleton (F : Finset ℕ) (u : F → Fin 2) :
    F.restrict ⁻¹' ({u} : Set (F → Fin 2)) =
      digitCylinder F (extendFiniteDigits F u) := by
  classical
  ext b
  simp only [Set.mem_preimage, Set.mem_singleton_iff, digitCylinder, Set.mem_setOf_eq]
  constructor
  · intro h k hk; simpa [extendFiniteDigits, hk] using congrFun h ⟨k, hk⟩
  · intro h; funext k; simpa [extendFiniteDigits, k.2] using h k.1 k.2

theorem comap_volume_eq_fairDigits : volume.comap positiveMersenneDigitValue = fairDigits := by
  unfold fairDigits
  refine (Measure.isProjectiveLimit_infinitePi (fun _ : ℕ => fairCoin)).unique ?_ |>.symm
  intro F
  apply Measure.ext_of_singleton
  intro u
  change ((volume.comap positiveMersenneDigitValue).map F.restrict)
      ({u} : Set (F → Fin 2)) = (Measure.pi fun _ : F => fairCoin) {u}
  rw [Measure.map_apply (Finset.measurable_restrict F) (measurableSet_singleton u),
    restrict_preimage_singleton]
  rw [Measure.comap_apply _ measurableEmbedding_mersenneCoding.injective
    (fun _ hs => measurableEmbedding_mersenneCoding.measurableSet_image.mpr hs)
    _ (measurableSet_digitCylinder F (extendFiniteDigits F u)), volume_image_digitCylinder]
  rw [← Set.univ_pi_singleton, Measure.pi_pi]
  simp [ENNReal.inv_pow]

theorem fairCoding_pushforward_eq_volume_restrict :
    Measure.map positiveMersenneDigitValue fairDigits = volume.restrict mersenneAchievementSet := by
  rw [← comap_volume_eq_fairDigits]
  ext s hs
  rw [Measure.map_apply measurableEmbedding_mersenneCoding.measurable hs,
    Measure.comap_apply _ measurableEmbedding_mersenneCoding.injective
      (fun _ ht => measurableEmbedding_mersenneCoding.measurableSet_image.mpr ht)
      _ (measurableEmbedding_mersenneCoding.measurable hs),
    Set.image_preimage_eq_inter_range, range_positiveMersenneDigitValue_eq,
    Measure.restrict_apply hs]

theorem measurePreserving_fairCoding :
    MeasurePreserving positiveMersenneDigitValue fairDigits (volume.restrict mersenneAchievementSet) :=
  ⟨continuous_positiveMersenneDigitValue.measurable, fairCoding_pushforward_eq_volume_restrict⟩

theorem fairCoding_cylinder_identity (F : Finset ℕ) (b : Digits) :
    fairDigits (digitCylinder F b) = volume (positiveMersenneDigitValue '' digitCylinder F b) := by
  rw [fairDigits_digitCylinder, volume_image_digitCylinder]

theorem fairCoding_preimage_null {s : Set ℝ} (hs : volume s = 0) :
    fairDigits (positiveMersenneDigitValue ⁻¹' s) = 0 := by
  have h := measurePreserving_fairCoding.quasiMeasurePreserving
  apply h.preimage_null
  rw [Measure.restrict_apply' isClosed_mersenneAchievementSet.measurableSet]
  exact measure_mono_null Set.inter_subset_left hs

theorem fairCoding_rational_values_null :
    fairDigits (positiveMersenneDigitValue ⁻¹' Set.range (fun q : ℚ => (q : ℝ))) = 0 := by
  apply fairCoding_preimage_null
  exact (Set.countable_range (fun q : ℚ => (q : ℝ))).measure_zero volume

end ErdosProblems.Erdos257.PaperGeometryCompletion
end
