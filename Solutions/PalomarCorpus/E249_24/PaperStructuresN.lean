/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.CarrySurvivorExtinction
import Erdos249257.DiagonalPincerCertificatesT64
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR21.DiagonalCertificateTableScales
import ErdosProblems.Erdos249.PaperCompleteR21.ShortWindowSupplyAndSixteenShifts
import Solutions.PalomarCorpus.E249_24.Statement

open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStructuresN
export PalomarCorpus.E249_24.Shared (certifiedKill periodLcm windowDiscrepancy)

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

end PalomarCorpus.E249.PaperStructuresN
