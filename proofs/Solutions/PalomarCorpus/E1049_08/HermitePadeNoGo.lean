/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.HermitePadeNoGo
import Solutions.PalomarCorpus.E1049_08.Statement

namespace PalomarCorpus.E1049.HermitePadeNoGo

theorem hpClearedGap_expansion (rho u : ℝ) :
    hpClearedGap rho (1 + rho + u) =
      -Real.pi ^ 2 * rho ^ 2 - Real.pi ^ 2 * rho * u -
        2 * Real.pi ^ 2 * rho - 2 * rho ^ 2 - 10 * rho * u -
        4 * rho - 6 * u ^ 2 - 8 * u :=
  ErdosProblems.Erdos1049.hpClearedGap_expansion rho u

theorem hpClearedGap_nonpos (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma ≤ 0 :=
  ErdosProblems.Erdos1049.hpClearedGap_nonpos rho sigma hrho hsigma

theorem hpClearedGap_eq_zero_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma = 0 ↔ rho = 0 ∧ sigma = 1 :=
  ErdosProblems.Erdos1049.hpClearedGap_eq_zero_iff rho sigma hrho hsigma

theorem rectangular_hp_threshold_le_classical (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma ≤ 1 / 2 - 1 / Real.pi ^ 2 :=
  ErdosProblems.Erdos1049.rectangular_hp_threshold_le_classical
    rho sigma hrho hsigma

theorem rectangular_hp_threshold_eq_classical_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma = 1 / 2 - 1 / Real.pi ^ 2 ↔
      rho = 0 ∧ sigma = 1 :=
  ErdosProblems.Erdos1049.rectangular_hp_threshold_eq_classical_iff
    rho sigma hrho hsigma

end PalomarCorpus.E1049.HermitePadeNoGo
