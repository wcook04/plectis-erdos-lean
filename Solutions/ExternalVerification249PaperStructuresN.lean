/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.DiagonalPincerCertificatesT64
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR21.DiagonalCertificateTableScales
import ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CarrySurvivorExtinction`, `Erdos249257.DiagonalPincerCertificatesT64`,
`Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.Erdos249.PaperCompleteR21.DiagonalCertificateTableScales`,
`ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts`.
-/

open Finset

namespace Erdos249257.ExternalVerification249PaperStructuresN

noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)

noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The local copy of `Erdos249257.TotientTailPeriodKiller.periodLcm` is the same function. -/
theorem periodLcm_transport_def : @periodLcm = @Erdos249257.TotientTailPeriodKiller.periodLcm := by
  first
  | (rfl; done)
  | (simp only [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm]; done)
  | (funext a; fun_induction periodLcm a <;> simp only [Erdos249257.TotientTailPeriodKiller.periodLcm, *]; done)
  | (funext a; induction a <;> simp only [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm, *]; done)
  | (funext a; simp [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm]; done)
  | (funext a b; fun_induction periodLcm a b <;> simp only [Erdos249257.TotientTailPeriodKiller.periodLcm, *]; done)
  | (funext a b; induction b <;> simp only [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm, *]; done)
  | (funext a b; simp [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm]; done)
  | (funext a b c; fun_induction periodLcm a b c <;> simp only [Erdos249257.TotientTailPeriodKiller.periodLcm, *]; done)
  | (funext a b c; induction c <;> simp only [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm, *]; done)
  | (funext a b c; simp [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm]; done)
  | (simp [periodLcm, Erdos249257.TotientTailPeriodKiller.periodLcm]; done)

theorem certifiedKill_diagonal_t64 :
    certifiedKill (periodLcm 64) (periodLcm 64) 93 := by
  simp only [periodLcm_transport_def]
  exact @Erdos249257.TotientTailPeriodKiller.certifiedKill_diagonal_t64

theorem certifiedKill_diagonal_t64_paper :
    certifiedKill (periodLcm 64) (periodLcm 64) 93 := by
  simp only [periodLcm_transport_def]
  exact @ErdosProblems.Erdos249.PaperCompleteR21.certifiedKill_diagonal_t64_paper

theorem shortWindowSupply_single_witness_six_ninetyThree (a₀ : ℕ) (ha₀ : a₀ ≤ 6) :
    a₀ ≤ 6 ∧ (93 : ℕ) < 2 * 2 ^ 6 ∧
      certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 := by
  simp only [periodLcm_transport_def]
  exact @ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_single_witness_six_ninetyThree a₀ ha₀

theorem shortWindowSupply_witness_eq_t64_certificate :
    certifiedKill (periodLcm (2 ^ 6)) (periodLcm (2 ^ 6)) 93 ↔
      certifiedKill (periodLcm 64) (periodLcm 64) 93 := by
  simp only [periodLcm_transport_def]
  exact @ErdosProblems.Erdos249.PaperCompleteR21.shortWindowSupply_witness_eq_t64_certificate

end Erdos249257.ExternalVerification249PaperStructuresN
