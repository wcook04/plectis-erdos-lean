/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.BooleanMobiusLocalRepair
import Erdos249257.HalfCylinderConcreteSeamAdapter
import Erdos249257.HalfCylinderIntegerGreedy
import ErdosProblems.Erdos257.PaperCompleteR21.ThreeBranchRowDynamics

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.BooleanMobiusLocalRepair`, `Erdos249257.HalfCylinderConcreteSeamAdapter`,
`Erdos249257.HalfCylinderIntegerGreedy`,
`ErdosProblems.Erdos257.PaperCompleteR21.ThreeBranchRowDynamics`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification257PaperStructuresAZ

noncomputable abbrev SeamRowWord (s : ℕ) := Fin (s - 2) → Bool

noncomputable def SeamRowWord.ofList {s : ℕ} (bits : List Bool) (hlen : bits.length = s - 2) :
    SeamRowWord s :=
  fun i => bits.get (Fin.cast hlen.symm i)

noncomputable def SeamRowWord.toNatWord {s : ℕ} (b : SeamRowWord s) : ℕ → Bool :=
  fun d => if h : 2 ≤ d ∧ d < s then b ⟨d - 2, by omega⟩ else false

noncomputable def integerGreedyBits : List ℕ → ℕ → List Bool
  | [], _ => []
  | w :: ws, C =>
      if w ≤ C then
        true :: integerGreedyBits ws (C - w)
      else
        false :: integerGreedyBits ws C

noncomputable def integerGreedyBits_length (weights : List ℕ) (C : ℕ) :
    (integerGreedyBits weights C).length = weights.length := by
  induction weights generalizing C with
  | nil => simp [integerGreedyBits]
  | cons w ws ih =>
      simp only [integerGreedyBits]
      split <;> simp [ih]

noncomputable def rowPulse (s d : ℕ) : ℕ :=
  (if d ∣ 2 * s + 2 then 1 else 0) +
    2 * (if d ∣ 2 * s + 1 then 1 else 0)

noncomputable def seamSubsetTarget (s : ℕ) : ℕ :=
  2 ^ (2 * s - 1) - 2 ^ s

noncomputable def truncatedMersenneWeight (s d : ℕ) : ℕ :=
  4 ^ s / (2 ^ d - 1)

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

noncomputable def seamWeightsFrom_eq_cons {s d : ℕ} (h : d < s) :
    seamWeightsFrom s d =
      truncatedMersenneWeight s d :: seamWeightsFrom s (d + 1) := by
  rw [seamWeightsFrom]
  simp [h]

noncomputable def seamWeightsFrom_eq_nil {s d : ℕ} (h : s ≤ d) :
    seamWeightsFrom s d = [] := by
  rw [seamWeightsFrom]
  simp [Nat.not_lt.mpr h]

noncomputable def seamWeightsFrom_length_eq (s d : ℕ) :
    (seamWeightsFrom s d).length = s - d := by
  by_cases hds : d < s
  · rw [seamWeightsFrom_eq_cons hds, List.length_cons,
      seamWeightsFrom_length_eq s (d + 1)]
    omega
  · rw [seamWeightsFrom_eq_nil (by omega)]
    simp
    omega
termination_by s - d
decreasing_by omega

noncomputable def seamWeights_length_eq (s : ℕ) :
    (seamWeights s).length = s - 2 := by
  unfold seamWeights
  exact seamWeightsFrom_length_eq s 2

noncomputable def seamGreedyWord (s : ℕ) : SeamRowWord s :=
  SeamRowWord.ofList
    (integerGreedyBits (seamWeights s) (seamSubsetTarget s))
    (by rw [integerGreedyBits_length, seamWeights_length_eq])

noncomputable def localMersenneQuotient (M d : ℕ) : ℕ :=
  2 ^ M / (2 ^ d - 1)

noncomputable def localPrefixQuotient (D : Finset ℕ) (M : ℕ) : ℕ :=
  ∑ d ∈ D, localMersenneQuotient M d

noncomputable def IsRowLower (n : ℕ) (D : Finset ℕ) : Prop :=
  D ⊆ Finset.Ico 2 n ∧
    localPrefixQuotient D (2 * n) ≤ seamSubsetTarget n ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        localPrefixQuotient S (2 * n) ≤ seamSubsetTarget n →
          localPrefixQuotient S (2 * n) ≤ localPrefixQuotient D (2 * n)

noncomputable def IsRowUpper (n : ℕ) (B : Finset ℕ) : Prop :=
  B ⊆ Finset.Ico 2 n ∧
    seamSubsetTarget n < localPrefixQuotient B (2 * n) ∧
      ∀ S, S ⊆ Finset.Ico 2 n →
        seamSubsetTarget n < localPrefixQuotient S (2 * n) →
          localPrefixQuotient B (2 * n) ≤ localPrefixQuotient S (2 * n)

noncomputable def rowSupport (n : ℕ) (b : SeamRowWord n) : Finset ℕ :=
  (Finset.Ico 2 n).filter (fun d => b.toNatWord d = true)

noncomputable def greedySupport (n : ℕ) : Finset ℕ := rowSupport n (seamGreedyWord n)

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList` is the same function. -/
theorem SeamRowWord_ofList_transport_def : @SeamRowWord.ofList = @Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList := by
  first
  | (rfl; done)
  | (simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (with_unfolding_all rfl; done)
  | (unfold SeamRowWord.ofList Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList; done)
  | (unfold SeamRowWord.ofList Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (ext x; simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a; fun_induction SeamRowWord.ofList a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a; induction a <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a; simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a b; fun_induction SeamRowWord.ofList a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction b <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction a generalizing b <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; induction b generalizing a <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b; simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (funext a b c; fun_induction SeamRowWord.ofList a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction c <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList, *]; done)
  | (funext a b c; simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)
  | (simp [SeamRowWord.ofList, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.ofList]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord` is the same function. -/
theorem SeamRowWord_toNatWord_transport_def : @SeamRowWord.toNatWord = @Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord := by
  first
  | (rfl; done)
  | (simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold SeamRowWord.toNatWord Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord; done)
  | (unfold SeamRowWord.toNatWord Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (ext x; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a; fun_induction SeamRowWord.toNatWord a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a; induction a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a; induction a <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a b; fun_induction SeamRowWord.toNatWord a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (funext a b c; fun_induction SeamRowWord.toNatWord a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def, *]; done)
  | (funext a b c; simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)
  | (simp [SeamRowWord.toNatWord, Erdos249257.HalfCylinderIntegerGreedy.SeamRowWord.toNatWord, SeamRowWord_ofList_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits` is the same function. -/
theorem integerGreedyBits_transport_def : @integerGreedyBits = @Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits := by
  first
  | (rfl; done)
  | (simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits; done)
  | (unfold integerGreedyBits Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (ext x; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a; fun_induction integerGreedyBits a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a; induction a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a; induction a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a b; fun_induction integerGreedyBits a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (funext a b c; fun_induction integerGreedyBits a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, *]; done)
  | (funext a b c; simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)
  | (simp [integerGreedyBits, Erdos249257.HalfCylinderIntegerGreedy.integerGreedyBits, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom` is the same function. -/
theorem seamWeightsFrom_transport_def : @seamWeightsFrom = @Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom := by
  first
  | (rfl; done)
  | (simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamWeightsFrom Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom; done)
  | (unfold seamWeightsFrom Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (ext x; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a; fun_induction seamWeightsFrom a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b; fun_induction seamWeightsFrom a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (funext a b c; fun_induction seamWeightsFrom a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, *]; done)
  | (funext a b c; simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)
  | (simp [seamWeightsFrom, Erdos249257.HalfCylinderIntegerGreedy.seamWeightsFrom, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamWeights` is the same function. -/
theorem seamWeights_transport_def : @seamWeights = @Erdos249257.HalfCylinderIntegerGreedy.seamWeights := by
  first
  | (rfl; done)
  | (simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamWeights Erdos249257.HalfCylinderIntegerGreedy.seamWeights; done)
  | (unfold seamWeights Erdos249257.HalfCylinderIntegerGreedy.seamWeights <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (ext x; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a; fun_induction seamWeights a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b; fun_induction seamWeights a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (funext a b c; fun_induction seamWeights a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, *]; done)
  | (funext a b c; simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)
  | (simp [seamWeights, Erdos249257.HalfCylinderIntegerGreedy.seamWeights, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord` is the same function. -/
theorem seamGreedyWord_transport_def : @seamGreedyWord = @Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord := by
  first
  | (rfl; done)
  | (simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold seamGreedyWord Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord; done)
  | (unfold seamGreedyWord Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (ext x; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a; fun_induction seamGreedyWord a <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; induction a <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a; simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b; fun_induction seamGreedyWord a b <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b; simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (funext a b c; fun_induction seamGreedyWord a b c <;> simp only [Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, *]; done)
  | (funext a b c; simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (simp [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [seamGreedyWord, Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def] <;> rfl; done)
  | (funext v1; unfold seamGreedyWord Erdos249257.HalfCylinderIntegerGreedy.seamGreedyWord <;> simp only [SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos257.PaperCompleteR21.greedySupport` is the same function. -/
theorem greedySupport_transport_def : @greedySupport = @ErdosProblems.Erdos257.PaperCompleteR21.greedySupport := by
  first
  | (rfl; done)
  | (simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold greedySupport ErdosProblems.Erdos257.PaperCompleteR21.greedySupport; done)
  | (unfold greedySupport ErdosProblems.Erdos257.PaperCompleteR21.greedySupport <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (ext x; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a; fun_induction greedySupport a <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a; induction a <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a; induction a <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a; induction a <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a; simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a b; fun_induction greedySupport a b <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b; simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (funext a b c; fun_induction greedySupport a b c <;> simp only [ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def, *]; done)
  | (funext a b c; simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (simp [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [greedySupport, ErdosProblems.Erdos257.PaperCompleteR21.greedySupport, SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def] <;> rfl; done)
  | (funext v1; unfold greedySupport ErdosProblems.Erdos257.PaperCompleteR21.greedySupport <;> simp only [SeamRowWord_ofList_transport_def, SeamRowWord_toNatWord_transport_def, integerGreedyBits_transport_def, seamWeightsFrom_transport_def, seamWeights_transport_def, seamGreedyWord_transport_def] <;> rfl; done)

theorem paper_dynamics {n : ℕ} (hn : 5 ≤ n) {D B D' : Finset ℕ}
    (hD : IsRowLower n D) (hB : IsRowUpper n B) (hD' : IsRowLower (n + 1) D')
    {r o pm pp rem : ℕ}
    (hr : localPrefixQuotient D (2 * n) + r = seamSubsetTarget n)
    (ho : seamSubsetTarget n + o = localPrefixQuotient B (2 * n))
    (hpm : pm = ∑ d ∈ D, rowPulse n d)
    (hpp : pp = ∑ d ∈ B, rowPulse n d)
    (hrem : localPrefixQuotient D' (2 * (n + 1)) + rem = seamSubsetTarget (n + 1)) :
    D = greedySupport n ∧
      pm ≤ 2 * (n - 2) ∧ pp ≤ 2 * (n - 2) ∧
      ((rem : ℤ) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          (2 : ℤ) ^ (n + 1) - 4 * (o : ℤ) - (pp : ℤ)
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ)
        else 4 * (r : ℤ) - 2 ^ (n + 1) - (pm : ℤ) - 4) ∧
      (((rem : ℚ) - 2 ^ (n + 1)) / 2 ^ (n + 1) =
        if 4 * (o : ℤ) + (pp : ℤ) ≤ 2 ^ (n + 1) then
          -((4 * (o : ℚ) + (pp : ℚ)) / 2 ^ (n + 1))
        else if 4 * (r : ℤ) + 2 ^ (n + 1) - (pm : ℤ) < 2 ^ (n + 2) + 4 then
          2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) + 2 - (pm : ℚ) / 2 ^ (n + 1)
        else 2 * (((r : ℚ) - 2 ^ n) / 2 ^ n) - ((pm : ℚ) + 4) / 2 ^ (n + 1)) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_dynamics n hn D B D' hD hB hD' r o pm pp rem hr ho hpm hpp hrem

theorem paper_greedySupport_greedy_rule {n : ℕ} (hn : 5 ≤ n) {d : ℕ}
    (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔
      truncatedMersenneWeight n d +
          ∑ e ∈ (greedySupport n).filter (fun e => e < d),
            truncatedMersenneWeight n e ≤ seamSubsetTarget n := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_greedy_rule n hn d hd hdn

theorem paper_greedySupport_isRowLower {n : ℕ} (hn : 5 ≤ n) :
    IsRowLower n (greedySupport n) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_isRowLower n hn

theorem paper_greedySupport_mem {n d : ℕ} (hd : 2 ≤ d) (hdn : d < n) :
    d ∈ greedySupport n ↔ seamGreedyWord n ⟨d - 2, by omega⟩ = true := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedySupport_mem n d hd hdn

theorem paper_greedy_step {n d : ℕ} (hd : d < n) (C : ℕ) :
    integerGreedyBits (seamWeightsFrom n d) C =
      (decide (truncatedMersenneWeight n d ≤ C)) ::
        integerGreedyBits (seamWeightsFrom n (d + 1))
          (if truncatedMersenneWeight n d ≤ C then
            C - truncatedMersenneWeight n d else C) := by
  set_option smartUnfolding false in
  with_unfolding_all exact @ErdosProblems.Erdos257.PaperCompleteR21.paper_greedy_step n d hd C

end Erdos249257.ExternalVerification257PaperStructuresAZ
