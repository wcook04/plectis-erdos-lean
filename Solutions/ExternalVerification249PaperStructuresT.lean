/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.FirstHarmonicPivot
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.ArgumentGraph.Results.Erdos249Endpoint
import ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCount

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `436f55ebdafa67e4af0fff79f621c13f2ded12bf` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.FirstHarmonicPivot`, `Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.ArgumentGraph.Results.Erdos249Endpoint`,
`ErdosProblems.Erdos249.PaperCompleteR21.UnassignedSmoothCount`.
-/

open Filter
open Finset
open Topology

namespace Erdos249257.ExternalVerification249PaperStructuresT

noncomputable def pivotOffset (L s : ℕ) : ℕ := L - s + 1

noncomputable def pivotArgument (N L s : ℕ) : ℕ := N + pivotOffset L s

noncomputable def pivotPrime (N L s : ℕ) : ℕ :=
  (pivotArgument N L s).primeFactors.toList.foldl Nat.max 1

noncomputable def pivotCofactor (N L s : ℕ) : ℕ :=
  pivotArgument N L s / pivotPrime N L s

noncomputable def pivotGoodCofactor (L s N : ℕ) (η : ℝ) : Prop :=
  η * pivotCofactor N L s ≤ Nat.totient (pivotCofactor N L s)

noncomputable def pivotSupplier (X L s N : ℕ) : Prop :=
  let p := pivotPrime N L s
  let m := pivotCofactor N L s
  p.Prime ∧ m * p = pivotArgument N L s ∧ 0 < m ∧
    m ≤ Nat.sqrt X / 2 ∧ 2 * Nat.sqrt X < p

noncomputable def pivotSupplierBases (X L s : ℕ) : Finset ℕ :=
  (Finset.Ico X (2 * X)).filter (pivotSupplier X L s)

noncomputable def pivotGoodBases (X L s : ℕ) (η : ℝ) : Finset ℕ :=
  (pivotSupplierBases X L s).filter fun N => pivotGoodCofactor L s N η

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))

noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)

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

noncomputable def exists_admissibleDepth (h s X : ℕ) : ∃ L, AdmissibleDepth h s X L :=
  ⟨_, admissibleDepth_witness h s X⟩

noncomputable def minimalDepth (h s X : ℕ) : ℕ := Nat.find (exists_admissibleDepth h s X)

theorem irrational_totient_series_of_goodBase_gap
    (hgap : ∀ h : ℕ, 0 < h → ∀ A : ℕ, ∃ X : ℕ, max A 1 ≤ X ∧
      (∑ N ∈ pivotGoodBases X (minimalDepth h 26 X) 26 (1 / 1000 : ℝ),
        windowFirstExp h N (minimalDepth h 26 X)).re ≤ (603 / 1000 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  first
  | (exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap hgap; done)
  | (set_option smartUnfolding false in
      exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap hgap; done)
  | (apply ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap <;> assumption; done)
  | (simpa only [AdmissibleDepth, admissibleDepth_witness, exists_admissibleDepth, minimalDepth, pivotArgument, pivotCofactor, pivotGoodBases, pivotGoodCofactor, pivotOffset, pivotPrime, pivotSupplier, pivotSupplierBases, windowDiscrepancy, windowFirstAngle, windowFirstExp] using ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap hgap; done)
  | (with_unfolding_all exact @ErdosProblems.Erdos249.PaperCompleteR21.irrational_totient_series_of_goodBase_gap hgap; done)

end Erdos249257.ExternalVerification249PaperStructuresT
