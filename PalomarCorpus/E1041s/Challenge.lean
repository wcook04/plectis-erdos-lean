/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band s

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial
open Finset
open Set

namespace PalomarCorpus.E1041.PaperStatementsS
open Polynomial
open Finset
open Set
/-- The scale that sends the two outermost roots of `T_n` to `-1` and `1`. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.endpointScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))
/-- The zeros of the endpoint-normalised scaled Chebyshev polynomial `q_*(x) = T_n(r_n x) / (2^(n-1) r_n^n)` of degree `n = m + 2`, listed in increasing order: `cos((2k+1)π/(2n)) / cos(π/(2n))`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.chebNode, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chebNode (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  Real.cos ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))
    / endpointScale (m + 2)
/-- The sharp normalised height. A later algebraic simplification rewrites this as `1 / (2^(n-1) * cos(pi/(2n))^n)`. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.comparisonBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
/-- The endpoint-normalised monic Chebyshev comparison polynomial. Local copy of ErdosProblems.Erdos1041.SharpCollinearChebyshev.monicScaledChebyshev, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def monicScaledChebyshev (n : ℕ) : ℝ[X] :=
  C (((2 : ℝ) ^ (n - 1))⁻¹) *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).scaleRoots (endpointScale n)⁻¹
/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.chebyshev_configuration_attains in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem chebyshev_configuration_attains {m : ℕ} (base dir : ℂ) (hdir : ‖dir‖ = 1)
    {R : ℝ} (hR : 0 < R) (f : ℂ[X])
    (hf : f = ∏ k : Fin (m + 2), (X - C (base + dir * ((R * chebNode m k : ℝ) : ℂ)))) :
    IsGreatest {d : ℝ | ∃ j k : Fin (m + 2),
        d = dist (base + dir * ((R * chebNode m j : ℝ) : ℂ))
                 (base + dir * ((R * chebNode m k : ℝ) : ℂ))} (2 * R) ∧
      ∀ i : Fin (m + 1),
        ∃ z ∈ segment ℝ (base + dir * ((R * chebNode m i.castSucc : ℝ) : ℂ))
                        (base + dir * ((R * chebNode m i.succ : ℝ) : ℂ)),
          ‖f.eval z‖ = comparisonBound (m + 2) * R ^ (m + 2) := by
  sorry
/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.exists_gap_le_comparisonBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_gap_le_comparisonBound {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1) (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ comparisonBound (m + 2) := by
  sorry
/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.monicScaledChebyshev_eq_prod in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem monicScaledChebyshev_eq_prod (m : ℕ) :
    monicScaledChebyshev (m + 2) = ∏ i : Fin (m + 2), (X - C (chebNode m i)) := by
  sorry
/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_equality_attained in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
              * (D / 2) ^ (m + 2) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsS
