/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GenericTailOrbitRigidity`,
`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel`,
`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodelEndpoint`,
`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates`.
-/

open scoped BigOperators
open Filter
open Set

namespace Erdos249257.ExternalVerification249PaperStatementsAW

noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

noncomputable def dyadicBase (B : ℕ) : ℚ :=
  2 - ∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℚ) / 2 ^ n

noncomputable def gamma (B P n : ℕ) : ℕ :=
  if n ≤ B then Nat.totient n else if P ∣ n then n - 1 else n

noncomputable def value (B P : ℕ) : ℚ := dyadicBase B - 1 / ((2 ^ P - 1 : ℕ) : ℚ)

noncomputable def discrepancy (c : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((c (N + h + j + 1) : ℤ) - c (N + j + 1)) * 2 ^ (L - 1 - j)

noncomputable def certificate (c : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < discrepancy c h N L % 2 ^ L ∧
  discrepancy c h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

noncomputable def windowPrefix (c : ℕ → ℕ) (N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (c (N + j + 1) : ℤ) * 2 ^ (L - 1 - j)

/-- States thm:gamma from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_series in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exact_series (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = 2 -
      (∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℝ) / 2 ^ n) -
      1 / ((2 : ℝ) ^ P - 1) := by
  sorry

/-- States thm:gamma from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.value_cast in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem value_cast (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = (value B P : ℝ) := by
  sorry

/-- States lem:gsound from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.certificate_sound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem certificate_sound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (h N L : ℕ) (hcert : certificate c h N L) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States lem:gperiod from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.generic_tail_period in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem generic_tail_period (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (p : ℤ) (e m h N : ℕ) (hm : 0 < m) (hN : e ≤ N)
    (hdvd : m ∣ 2 ^ h - 1)
    (hS : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * m)) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry

/-- States lem:gsound from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_difference in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem scaled_difference (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    (2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ) =
      binaryCoeffTail c (N + h + L) - binaryCoeffTail c (N + L) := by
  sorry

/-- States lem:gperiod from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_tail_split in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem scaled_tail_split (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (N L : ℕ) :
    (2 : ℝ) ^ L * binaryCoeffTail c N =
      (windowPrefix c N L : ℝ) + binaryCoeffTail c (N + L) := by
  sorry

/-- States lem:gsound from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.truncation_error_bound in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem truncation_error_bound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    |(2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ)| ≤ (N : ℝ) + h + L + 2 := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsAW
