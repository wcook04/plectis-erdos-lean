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
`ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterWhole`.
-/

open Polynomial
open Finset
open Set

namespace Erdos249257.ExternalVerification1041PaperStatementsE

noncomputable def CollinearDiameterBound (n : ℕ) (K : ℝ) : Prop :=
  ∀ base dir : ℂ, ‖dir‖ = 1 → ∀ (y : Fin n → ℝ) (f : ℂ[X]),
    f = (∏ k, (X - C (base + dir * (y k : ℂ)))) → ∀ D : ℝ,
      IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
            ‖f.eval z‖ ≤ K * (D / 2) ^ n

/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record
and the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.collinearDiameterBound_sharpConstant in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem collinearDiameterBound_sharpConstant {n : ℕ} (hn : 2 ≤ n) :
    CollinearDiameterBound n
      (1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n)) := by
  sorry

/-- States cor:collinear-erdos-1041, res:sharp-collinear-root-diameter,
thm:sharp-collinear-diameter from the long record and the short record for Erdős problem
#1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.exists_collinear_factorisation in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_collinear_factorisation (base dir : ℂ) :
    ∀ (n : ℕ) (f : ℂ[X]), f.IsMonicOfDegree n →
      (∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) →
      ∃ y : Fin n → ℝ, f = ∏ k : Fin n, (X - C (base + dir * (y k : ℂ))) := by
  sorry

/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record
and the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.sharpConstant_le_of_collinearDiameterBound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem sharpConstant_le_of_collinearDiameterBound {n : ℕ} (hn : 2 ≤ n) {K : ℝ}
    (hK : CollinearDiameterBound n K) :
    1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) ≤ K := by
  sorry

/-- States cor:collinear-erdos-1041, res:sharp-collinear-root-diameter,
thm:sharp-collinear-diameter from the long record and the short record for Erdős problem
#1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sharp_collinear_root_diameter {n : ℕ} (hn : 2 ≤ n)
    (base dir : ℂ) (hdir : ‖dir‖ = 1) (y : Fin n → ℝ) (f : ℂ[X])
    (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ)))) (D : ℝ)
    (hD : IsGreatest {d : ℝ | ∃ j k : Fin n,
        d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D) :
    ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
      (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
      dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
      ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
        ‖f.eval z‖
          ≤ 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) * (D / 2) ^ n := by
  sorry

/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record
and the short record for Erdős problem #1041. Transported from
ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter_monic in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem sharp_collinear_root_diameter_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) :
    ∃ y : Fin n → ℝ, f = (∏ k, (X - C (base + dir * (y k : ℂ)))) ∧
      ∀ D : ℝ, IsGreatest {d : ℝ | ∃ j k : Fin n,
          d = dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ))} D →
        ∃ j k : Fin n, j ≠ k ∧ y j ≤ y k ∧
          (∀ l : Fin n, y l ≤ y j ∨ y k ≤ y l) ∧
          dist (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) ≤ D ∧
          ∀ z ∈ segment ℝ (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)),
            ‖f.eval z‖
              ≤ 1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n)
                * (D / 2) ^ n := by
  sorry

end Erdos249257.ExternalVerification1041PaperStatementsE
