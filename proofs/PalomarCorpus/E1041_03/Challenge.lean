/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1041, record section 7.1: collinear roots and Chebyshev comparison

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1041, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. A degree-seven counterexample due to ani,
formalised in this corpus, refutes the total-variation formulation of Erdős problem
#1041; the theorems in this entry keep their stated hypotheses.
-/

open Set
open Polynomial
open Finset
open scoped NNReal
open scoped ENNReal

namespace PalomarCorpus.E1041_03.Shared
/-- The real number cos (π / (2 n)). For n ≥ 2 it is the scale that carries the two outermost zeros of the degree-n Chebyshev polynomial to -1 and 1. -/
noncomputable def endpointScale (n : ℕ) : ℝ :=
  Real.cos (Real.pi / (2 * (n : ℝ)))
/-- The sharp endpoint-normalised Chebyshev height C n = 1 / (2 ^ (n - 1) cos ^ n (π / (2 n))), written as the absolute value of (2 ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n. For n ≥ 2 it is the maximum modulus on [-1, 1] of the monic polynomial T n (cos (π / (2 n)) x) / (2 ^ (n - 1) cos ^ n (π / (2 n))), whose extreme zeros are -1 and 1. The exponent n - 1 is natural subtraction, and the absolute value is cosmetic because the expression is positive for every n ≥ 2; at n = 1 the inverse of cos (π / 2) is 0 by the Lean convention and the value is 0. -/
noncomputable def comparisonBound (n : ℕ) : ℝ :=
  |((2 : ℝ) ^ (n - 1))⁻¹ * (endpointScale n)⁻¹ ^ n|
end PalomarCorpus.E1041_03.Shared

namespace PalomarCorpus.E1041.PaperStatementsI
open Set
open Polynomial
export PalomarCorpus.E1041_03.Shared (comparisonBound endpointScale)
/-- States prop:sharp-collinear-chebyshev-comparator from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.SharpCollinearChebyshev.exists_peak_le_comparisonBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_peak_le_comparisonBound
    {m : ℕ} {p : ℝ[X]} {c : Fin (m + 1) → ℝ}
    (hp : p.IsMonicOfDegree (m + 2))
    (hc : StrictMono c) (ha : -1 < c 0) (hb : c (Fin.last m) < 1)
    (hpa : p.eval (-1) = 0) (hpb : p.eval 1 = 0)
    (hpalt : ∀ i : Fin m,
      p.eval (c i.castSucc) * p.eval (c i.succ) < 0)
    (hc_mem : ∀ i : Fin (m + 1), |c i| ≤ 1) :
    ∃ i : Fin (m + 1), |p.eval (c i)| ≤ comparisonBound (m + 2) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsI

namespace PalomarCorpus.E1041.PaperStatementsE
open Polynomial
open Finset
open Set
/-- The conclusion of the sharp collinear diameter theorem, with the constant left as a parameter `K`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.CollinearDiameterBound, restated so the compared statements elaborate against Mathlib alone. -/
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
/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.collinearDiameterBound_sharpConstant in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem collinearDiameterBound_sharpConstant {n : ℕ} (hn : 2 ≤ n) :
    CollinearDiameterBound n
      (1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n)) := by
  sorry
/-- States cor:collinear-erdos-1041, res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.exists_collinear_factorisation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_collinear_factorisation (base dir : ℂ) :
    ∀ (n : ℕ) (f : ℂ[X]), f.IsMonicOfDegree n →
      (∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ)) →
      ∃ y : Fin n → ℝ, f = ∏ k : Fin n, (X - C (base + dir * (y k : ℂ))) := by
  sorry
/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.sharpConstant_le_of_collinearDiameterBound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sharpConstant_le_of_collinearDiameterBound {n : ℕ} (hn : 2 ≤ n) {K : ℝ}
    (hK : CollinearDiameterBound n K) :
    1 / (2 ^ (n - 1) * Real.cos (Real.pi / (2 * (n : ℝ))) ^ n) ≤ K := by
  sorry
/-- States cor:collinear-erdos-1041, res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
/-- States res:sharp-collinear-root-diameter, thm:sharp-collinear-diameter from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.sharp_collinear_root_diameter_monic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
end PalomarCorpus.E1041.PaperStatementsE

namespace PalomarCorpus.E1041.PaperStatementsS
open Polynomial
open Finset
open Set
export PalomarCorpus.E1041_03.Shared (comparisonBound endpointScale)
/-- The zeros of the endpoint-normalised scaled Chebyshev polynomial `q_*(x) = T_n(r_n x) / (2^(n-1) r_n^n)` of degree `n = m + 2`, listed in increasing order: `cos((2k+1)π/(2n)) / cos(π/(2n))`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.chebNode, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chebNode (m : ℕ) (i : Fin (m + 2)) : ℝ :=
  Real.cos ((2 * ((m + 1 - (i : ℕ) : ℕ) : ℝ) + 1) * Real.pi / (2 * ((m + 2 : ℕ) : ℝ)))
    / endpointScale (m + 2)
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

namespace PalomarCorpus.E1041.PaperStatementsT
open Polynomial
open Finset
open Set
open scoped NNReal
open scoped ENNReal
/-- The geometric conclusion used by the paper: a continuous rectifiable curve with specified endpoints, containment at every parameter, and a strict variation bound. Local copy of ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
/-- States cor:collinear-erdos-1041 from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem collinear_erdos_1041 {n : ℕ} (hn : 2 ≤ n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (y : Fin n → ℝ) (f : ℂ[X]) (hf : f = ∏ k, (X - C (base + dir * (y k : ℂ))))
    (hdisc : ∀ k : Fin n, ‖base + dir * (y k : ℂ)‖ < 1) :
    ∃ j k : Fin n, j ≠ k ∧
      ConnectedBelow f.eval 1 2
        (base + dir * (y j : ℂ)) (base + dir * (y k : ℂ)) := by
  sorry
/-- States cor:collinear-erdos-1041 from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.collinear_erdos_1041_monic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem collinear_erdos_1041_monic {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.IsMonicOfDegree n) (base dir : ℂ) (hdir : ‖dir‖ = 1)
    (hcol : ∀ z ∈ f.roots, ∃ t : ℝ, z = base + dir * (t : ℂ))
    (hdisc : ∀ z ∈ f.roots, ‖z‖ < 1) :
    ∃ a b : ℂ, a ∈ f.roots ∧ b ∈ f.roots ∧
      ConnectedBelow f.eval 1 2 a b := by
  sorry
end PalomarCorpus.E1041.PaperStatementsT
