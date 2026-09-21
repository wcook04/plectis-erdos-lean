/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterWhole`,
`ErdosProblems.Erdos1041.SharpCollinearChebyshev`.
-/

open Polynomial
open Finset
open Set

namespace Erdos249257.ExternalVerification1041PaperStatementsS

noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))

noncomputable def chebNode (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  Real.cos ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))
    / endpointScale (m + 2)

noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|

noncomputable def monicScaledChebyshev (n : ℕ) : ℝ[X] :=
  C (((2 : ℝ) ^ (n - 1))⁻¹) *
    (Polynomial.Chebyshev.T ℝ (n : ℤ)).scaleRoots (endpointScale n)⁻¹

/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record
and the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.chebyshev_configuration_attains in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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

/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record
and the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.exists_gap_le_comparisonBound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_gap_le_comparisonBound {m : ℕ} (Y : Fin (m + 2) → ℝ)
    (hY : StrictMono Y) (hY0 : Y 0 = -1) (hY1 : Y (Fin.last (m + 1)) = 1) :
    ∃ i : Fin (m + 1), ∀ x ∈ Icc (Y i.castSucc) (Y i.succ),
      |∏ j, (x - Y j)| ≤ comparisonBound (m + 2) := by
  sorry

/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record
and the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.monicScaledChebyshev_eq_prod in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem monicScaledChebyshev_eq_prod (m : ℕ) :
    monicScaledChebyshev (m + 2) = ∏ i : Fin (m + 2), (X - C (chebNode m i)) := by
  sorry

/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record
and the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_equality_attained in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
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

end Erdos249257.ExternalVerification1041PaperStatementsS
