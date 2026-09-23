/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `a25cb360bef8dd818dde14b5fb752244304af354` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR11.CubicIntegralNormalisation`,
`ErdosProblems.Erdos243.PaperCompleteR11.CubicZeroDensityShape`,
`ErdosProblems.Erdos243.PaperCompleteR21.CubicRateExclusionChain`,
`ErdosProblems.Erdos243.PaperCompleteR21.SquareSpecialisationUnconditional`,
`ErdosProblems.Erdos243.PaperCompleteR9.PolynomialCorrections`.
-/

namespace Erdos249257.ExternalVerification243PaperStructuresAC

noncomputable def exceptionFinset (E : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n ↦ n ∈ E)

noncomputable def exceptionCount (E : Set ℕ) (X : ℕ) : ℕ :=
  (exceptionFinset E X).card

noncomputable def ZeroLowerDensity (E : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ X : ℕ,
    N ≤ X ∧ (exceptionCount E X : ℝ) < ε * (X : ℝ)

noncomputable def risingBinomial (n : ℕ) : ℤ := ((n + 2).choose 3 : ℤ)

noncomputable def SquareSpecialisation : Prop :=
  ∀ (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀) (f H : Polynomial ℚ),
    Irreducible f → Polynomial.aeval α f = 0 → Polynomial.aeval α H ≠ 0 →
    ∀ (d : ℕ), 0 < d → ∀ G J : Polynomial ℤ,
    G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f →
    J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H →
    (∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
        (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
        (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
          IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) →
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = Polynomial.aeval α H

/-- States long243:eq:cubicorbit, long243:res:cubicexclusion from the long record for Erdős
problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.cubic_exclusion_unconditional in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cubic_exclusion_unconditional
    (a C D : ℕ → ℤ) (ha : ∀ n, 0 < a n) (hC : ∀ n, 0 < C n) (hD : ∀ n, 0 < D n)
    (hCrec : ∀ n, C (n + 1) = a n * C n - D n)
    (hDrec : ∀ n, D (n + 1) = a n * D n)
    (A B : ℚ) (hA : 0 < A) :
    (∃ dens : ℝ, 0 < dens ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        dens * (X : ℝ) ≤ (exceptionCount
          {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
          (X + 1) : ℝ)) ∧
      ¬ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℚ) = A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B := by
  sorry

/-- States long243:res:cubicrate, res:cubicrate from the long record and the short record for
Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem cubic_rate_irrationality_unconditional
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv := by
  sorry

/-- States long243:res:squarespec from the long record for Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem squareSpecialisation : SquareSpecialisation := by
  sorry

/-- States long243:res:transportsquare from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.transport_square_unconditional in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem transport_square_unconditional
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀)
    (hroot : α ^ 3 = α - algebraMap ℚ L₀ (6 * (c : ℚ) / (m : ℚ))) :
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = α ^ 2 - 1 := by
  sorry

end Erdos249257.ExternalVerification243PaperStructuresAC
