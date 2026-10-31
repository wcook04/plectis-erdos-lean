/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.ThreeBranchRowDynamics

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a declaration of the substantive development in this repository,
at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos: a refereed paper statement, or a lemma or a proof
field that a copied definition names, as its documentation says. The definitions are local
copies of the source definitions, so the statements elaborate against Mathlib alone. This
module is a comparison interface over that development, not the development itself. The
mathematics is developed in
`Erdos249257.BooleanMobiusLocalRepair`, `Erdos249257.HalfCylinderConcreteSeamAdapter`,
`Erdos249257.HalfCylinderIntegerGreedy`,
`ErdosProblems.Erdos257.PaperCompleteR21.ThreeBranchRowDynamics`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresBX

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

noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool

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

noncomputable def seamAboveWord (s : ℕ) (hs : 5 ≤ s) :
    SeamRowWord s :=
  Classical.choose (exists_seamWord_minimal_above hs)

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

noncomputable def IsRowUpper (n : ℕ) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Ico 2 n ∧
    seamSubsetTarget n < localPrefixQuotient B (2 * n) ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        seamSubsetTarget n < localPrefixQuotient S (2 * n) →
          localPrefixQuotient B (2 * n) ≤ localPrefixQuotient S (2 * n)

noncomputable def rowSupport (n : ℕ) (b : SeamRowWord n) : Finset ℕ :=
  (Finset.Ico 2 n).filter (fun d => b.toNatWord d = true)

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

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord` is the same function. -/
theorem SeamRowWord_toNatWord_transport_def : @SeamRowWord.toNatWord = @Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord := by
  first
  | (rfl; done)
  | (simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (with_unfolding_all rfl; done)
  | (unfold SeamRowWord.toNatWord Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord; done)
  | (unfold SeamRowWord.toNatWord Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (ext x; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a; fun_induction SeamRowWord.toNatWord a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a; induction a <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a b; fun_induction SeamRowWord.toNatWord a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction a generalizing b <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; induction b generalizing a <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (funext a b c; fun_induction SeamRowWord.toNatWord a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, *]; done)
  | (funext a b c; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)
  | (simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord]; done)

theorem paper_upperSupport_isRowUpper {n : ℕ} (hn : 5 ≤ n) :
    IsRowUpper n (rowSupport n (seamAboveWord n hn)) := @ErdosProblems.Erdos257.PaperCompleteR21.paper_upperSupport_isRowUpper n hn

end Erdos249257.ExternalVerification257PaperStructuresBX
