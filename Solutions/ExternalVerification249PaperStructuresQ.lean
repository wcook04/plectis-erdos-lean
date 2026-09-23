/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.FirstHarmonicPivot
import ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCount
import ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCut

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `a25cb360bef8dd818dde14b5fb752244304af354` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.FirstHarmonicPivot`,
`ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCount`,
`ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCut`.
-/

open Finset
open Filter
open Topology

namespace Erdos249257.ExternalVerification249PaperStructuresQ

noncomputable def pivotOffset (L s : ℕ) : ℕ := L - s + 1

noncomputable def pivotArgument (N L s : ℕ) : ℕ := N + pivotOffset L s

noncomputable def pivotPrime (N L s : ℕ) : ℕ :=
  (pivotArgument N L s).primeFactors.toList.foldl Nat.max 1

noncomputable def pivotCofactor (N L s : ℕ) : ℕ :=
  pivotArgument N L s / pivotPrime N L s

noncomputable def pivotSupplier (X L s N : ℕ) : Prop :=
  let p := pivotPrime N L s
  let m := pivotCofactor N L s
  p.Prime ∧ m * p = pivotArgument N L s ∧ 0 < m ∧
    m ≤ Nat.sqrt X / 2 ∧ 2 * Nat.sqrt X < p

noncomputable instance instDecidablePivotSupplier (X L s N : ℕ) : Decidable (pivotSupplier X L s N) := by
  unfold pivotSupplier
  infer_instance

noncomputable def pivotSupplierBases (X L s : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (pivotSupplier X L s)

noncomputable def AdmissibleDepth (h s X L : ℕ) : Prop :=
  h ≤ L - s ∧ 16 * (2 * X + h + L + 2) ≤ 2 ^ L

noncomputable def admissibleDepth_witness (h s X : ℕ) :
    AdmissibleDepth h s X (h + s + Nat.log 2 X + 10) := by
  refine ⟨by omega, ?_⟩
  have hA : h + s + 1 ≤ 2 ^ (h + s) := Nat.lt_two_pow_self
  have hB : X + 1 ≤ 2 * 2 ^ (Nat.log 2 X) := by
    have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) X
    rw [pow_succ] at this; omega
  have hlog : Nat.log 2 X ≤ X := Nat.log_le_self 2 X
  have hpow : 2 ^ (h + s + Nat.log 2 X + 10) = 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by
    rw [pow_add, pow_add]; norm_num
  rw [hpow]
  have hprod : (h + s + 1) * (X + 1) ≤ 2 ^ (h + s) * (2 * 2 ^ (Nat.log 2 X)) :=
    Nat.mul_le_mul hA hB
  have h1 : 16 * (2 * X + h + (h + s + Nat.log 2 X + 10) + 2)
      ≤ 512 * ((h + s + 1) * (X + 1)) := by
    nlinarith [Nat.zero_le (h * X), Nat.zero_le (s * X)]
  have h2 : 512 * ((h + s + 1) * (X + 1)) ≤ 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by
    calc 512 * ((h + s + 1) * (X + 1))
        ≤ 512 * (2 ^ (h + s) * (2 * 2 ^ (Nat.log 2 X))) := Nat.mul_le_mul_left _ hprod
      _ = 2 ^ (h + s) * 2 ^ (Nat.log 2 X) * 1024 := by ring
  omega

noncomputable def dickmanCut (X t : ℕ) : ℝ :=
  4 * Real.sqrt X + 2 * (t : ℝ) / Real.sqrt X

noncomputable def exists_admissibleDepth (h s X : ℕ) : ∃ L, AdmissibleDepth h s X L :=
  ⟨_, admissibleDepth_witness h s X⟩

noncomputable instance instDecidablePredNatAdmissibleDepth (h s X : ℕ) : DecidablePred (AdmissibleDepth h s X) := fun L => by
  unfold AdmissibleDepth; infer_instance

noncomputable def minimalDepth (h s X : ℕ) : ℕ := Nat.find (exists_admissibleDepth h s X)

noncomputable def minimalOffset (h s X : ℕ) : ℕ := pivotOffset (minimalDepth h s X) s

noncomputable def minimalCut (h s X : ℕ) : ℝ := dickmanCut X (minimalOffset h s X)

noncomputable def smoothCount (x : ℕ) (y : ℝ) : ℕ :=
  ((Icc 1 x).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card

theorem prop_dickman (h s : ℕ) :
    (∀ X, AdmissibleDepth h s X (minimalDepth h s X) ∧
        ∀ L, AdmissibleDepth h s X L → minimalDepth h s X ≤ L) ∧
    (∀ X, minimalOffset h s X ≤ h + Nat.log 2 X + 11) ∧
    (∀ X N, 0 < X → N ∈ Ico X (2 * X) → N ∉ pivotSupplierBases X (minimalDepth h s X) s →
      ∀ hn : 1 < N + minimalOffset h s X,
        (((N + minimalOffset h s X).primeFactors.max'
            (Nat.nonempty_primeFactors.mpr hn) : ℕ) : ℝ) ≤ minimalCut h s X) ∧
    (∀ X, 0 < X →
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        ≤ (smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) ∧
    Tendsto (fun X : ℕ =>
        ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) / X)
      atTop (𝓝 (1 - Real.log 2)) ∧
    (∀ᶠ X : ℕ in atTop,
      ((smoothCount (2 * X + minimalOffset h s X - 1) (minimalCut h s X) : ℝ)
          - smoothCount (X + minimalOffset h s X - 1) (minimalCut h s X)) < 8 / 25 * X ∧
      ((((Ico X (2 * X)).filter
          (fun N => N ∉ pivotSupplierBases X (minimalDepth h s X) s)).card : ℕ) : ℝ)
        < 8 / 25 * X) := @ErdosProblems.Erdos249.PaperCompleteR21.prop_dickman h s

end Erdos249257.ExternalVerification249PaperStructuresQ
