/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterWhole
import ErdosProblems.Erdos1041.SharpCollinearChebyshev
import Solutions.PalomarCorpus.E1041_03.Statement

open Polynomial
open Finset
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsS
export PalomarCorpus.E1041_03.Shared (comparisonBound endpointScale)

theorem chebyshev_configuration_attains {m : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1)
    {R : ℝ} (hR : 0 < R) (f : ℂ[X])
    (hf : f = ∏ k : Fin (m + 2), (X - C (base + dir * ((R * chebNode m k : ℝ) : ℂ)))) :
    IsGreatest {d : ℝ | ∃ j k : Fin (m + 2),
        d = dist (base + dir * ((R * chebNode m j : ℝ) : ℂ))
                 (base + dir * ((R * chebNode m k : ℝ) : ℂ))} (2 * R) ∧
      ∀ i : Fin (m + 1),
        ∃ z ∈ segment ℝ (base + dir * ((R * chebNode m i.castSucc : ℝ) : ℂ))
                        (base + dir * ((R * chebNode m i.succ : ℝ) : ℂ)),
          ‖f.eval z‖ = comparisonBound (m + 2) * R ^ (m + 2) := @ErdosProblems.Erdos1041.PaperCompleteR21.chebyshev_configuration_attains m base dir hdir R hR f hf

theorem exists_gap_le_comparisonBound {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1) (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ comparisonBound (m + 2) := @ErdosProblems.Erdos1041.PaperCompleteR21.exists_gap_le_comparisonBound m Y hY hY0 hY1

theorem monicScaledChebyshev_eq_prod (m : ℕ) :
    monicScaledChebyshev (m + 2) = ∏ i : Fin (m + 2), (X - C (chebNode m i)) := @ErdosProblems.Erdos1041.PaperCompleteR21.monicScaledChebyshev_eq_prod m

theorem sharp_collinear_equality_attained {m : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1)
    {D : ℝ} (hD : 0 < D) (f : ℂ[X])
    (hf : f = ∏ k : Fin (m + 2), (X - C (base + dir * ((D / 2 * chebNode m k : ℝ) : ℂ)))) :
    IsGreatest {d : ℝ | ∃ j k : Fin (m + 2),
        d = dist (base + dir * ((D / 2 * chebNode m j : ℝ) : ℂ))
                 (base + dir * ((D / 2 * chebNode m k : ℝ) : ℂ))} D ∧
      ∀ i : Fin (m + 1),
        ∃ z ∈ segment ℝ (base + dir * ((D / 2 * chebNode m i.castSucc : ℝ) : ℂ))
                        (base + dir * ((D / 2 * chebNode m i.succ : ℝ) : ℂ)),
          ‖f.eval z‖
            = 1 / (2 ^ ((m + 2) - 1)
                * Real.cos (Real.pi / (2 * ((m + 2 : ℕ) : ℝ))) ^ (m + 2))
              * (D / 2) ^ (m + 2) := @ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_equality_attained m base dir hdir D hD f hf

end PalomarCorpus.E1041.PaperStatementsS
