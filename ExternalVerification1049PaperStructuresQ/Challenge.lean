/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.PaperCompleteR21.SourceCoefficientHeights`,
`ErdosProblems.Erdos1049.PaperLongCapR9`, `ErdosProblems.Erdos1049.PaperOmegaIndicatorR7`,
`ErdosProblems.Erdos1049.QBinomialUnitIdentity`,
`ErdosProblems.Erdos1049.SourceBClearingR12`, `ErdosProblems.Erdos1049.SourceBMonomialR12`,
`ErdosProblems.Erdos1049.SourceBTopDegreeR13`,
`ErdosProblems.Erdos1049.SourcePolynomialR11`.
-/

open Filter
open Polynomial
open scoped BigOperators
open Finset
open Asymptotics
open scoped Topology

namespace Erdos249257.ExternalVerification1049PaperStructuresQ

noncomputable def sourceAExponent (n s : ℕ) : ℕ :=
  2 * n ^ 2 + (n + 1) * s + s.choose 2

noncomputable def gaussBinom {R : Type*} [CommRing R] (q : R) : ℕ → ℕ → R
  | 0, 0 => 1
  | 0, Nat.succ _ => 0
  | Nat.succ _, 0 => 1
  | n + 1, k + 1 =>
      gaussBinom q n (k + 1) +
        if k ≤ n then q ^ (n - k) * gaussBinom q n k else 0

noncomputable def sourceGaussianProduct (n s : ℕ) : ℤ[X] :=
  gaussBinom X (14 * n + s) (12 * n) *
    gaussBinom X (13 * n) (13 * n - s)

noncomputable def sourceM (n : ℕ) : ℕ := 266 * n ^ 2 + 34 * n + 1

noncomputable def sourceASummand (n s : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) * X ^ (sourceM n + sourceAExponent n s) *
    sourceGaussianProduct n s

noncomputable def sourceNormalisedASummand (n s : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) * X ^ sourceAExponent n s * sourceGaussianProduct n s

noncomputable def sourceAWithoutMonomial (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1), sourceNormalisedASummand n s

noncomputable def omegaWeight (x : ℝ) : ℤ :=
  max 0 (max (⌊14 * x⌋ + ⌊13 * x⌋ - ⌊12 * x⌋ - ⌊15 * x⌋)
    (2 * ⌊14 * x⌋ - ⌊13 * x⌋ - ⌊15 * x⌋))

noncomputable def sourceWeight (n l : ℕ) : ℤ :=
  omegaWeight ((n : ℝ) / (l : ℝ))

noncomputable def sourceComplement (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n),
    if sourceWeight n l = 0 then cyclotomic l ℤ else 1

noncomputable def sourceOmega (n : ℕ) : ℤ[X] :=
  ∏ l ∈ Finset.Icc 1 (15 * n), (cyclotomic l ℤ) ^ (sourceWeight n l).toNat

noncomputable def sourceU (n : ℕ) : ℤ[X] :=
  sourceComplement n * sourceAWithoutMonomial n

noncomputable def sourceShiftedASummand (n s j : ℕ) : ℤ[X] :=
  C ((-1 : ℤ) ^ s) *
    X ^ (sourceM n + sourceAExponent n s - j * (2 * n + s)) *
    sourceGaussianProduct n s

noncomputable def sourceDQuotient (n j : ℕ) : ℤ[X] :=
  ∏ l ∈ (Finset.Icc 1 (15 * n) \ j.divisors), cyclotomic l ℤ

noncomputable def sourceClearedB (n : ℕ) : ℤ[X] :=
  ∑ s ∈ Finset.range (13 * n + 1),
    ((∑ l ∈ Finset.Icc 1 (2 * n + s),
        sourceASummand n s * sourceDQuotient n l) +
      (∑ j ∈ Finset.Icc 1 (14 * n),
        sourceShiftedASummand n s j * sourceDQuotient n j))

noncomputable def sourceBWithoutMonomial (n : ℕ) : ℤ[X] :=
  sourceClearedB n /ₘ ((X : ℤ[X]) ^ sourceM n)

noncomputable def sourceV (n : ℕ) : ℤ[X] :=
  sourceBWithoutMonomial n /ₘ sourceOmega n

noncomputable def maxCoeffNat (P : Polynomial ℤ) : ℕ :=
  P.support.sup (fun i => (P.coeff i).natAbs)

noncomputable def maxPairHeight (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℝ :=
  (max (maxCoeffNat (U n)) (maxCoeffNat (V n)) : ℕ)

/-- States long1049:res:sourceheight from the long record for Erdős problem #1049. Transported
from ErdosProblems.Erdos1049.PaperCompleteR21.exists_quadratic_source_height_bound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_quadratic_source_height_bound :
    ∃ h : ℝ, ∀ n : ℕ, 1 ≤ n →
      Real.log
          ((max (maxCoeffNat (sourceU n))
            (maxCoeffNat (sourceV n)) : ℕ) : ℝ) ≤
        h * (n : ℝ) ^ 2 := by
  sorry

/-- States long1049:res:sourceheight from the long record for Erdős problem #1049. Transported
from ErdosProblems.Erdos1049.PaperCompleteR21.maxPairHeight_source_eq in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem maxPairHeight_source_eq (n : ℕ) :
    maxPairHeight sourceU sourceV n =
      ((max (maxCoeffNat (sourceU n))
        (maxCoeffNat (sourceV n)) : ℕ) : ℝ) := by
  sorry

end Erdos249257.ExternalVerification1049PaperStructuresQ
