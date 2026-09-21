/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band w

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open Filter
open Set

namespace PalomarCorpus.E249.PaperStatementsAW
open scoped BigOperators
open Filter
open Set
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.dyadicBase, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBase (B : ℕ) : ℚ :=
  2 - ∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℚ) / 2 ^ n
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def gamma (B P n : ℕ) : ℕ :=
  if n ≤ B then Nat.totient n else if P ∣ n then n - 1 else n
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.value, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def value (B P : ℕ) : ℚ := dyadicBase B - 1 / ((2 ^ P - 1 : ℕ) : ℚ)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.discrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def discrepancy (c : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((c (N + h + j + 1) : ℤ) - c (N + j + 1)) * 2 ^ (L - 1 - j)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.certificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certificate (c : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < discrepancy c h N L % 2 ^ L ∧
  discrepancy c h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.windowPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowPrefix (c : ℕ → ℕ) (N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L, (c (N + j + 1) : ℤ) * 2 ^ (L - 1 - j)
/-- States thm:gamma from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exact_series (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = 2 -
      (∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℝ) / 2 ^ n) -
      1 / ((2 : ℝ) ^ P - 1) := by
  sorry
/-- States thm:gamma from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.value_cast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem value_cast (B P : ℕ) (hBP : B < P) :
    binaryCoeffSeries (gamma B P) = (value B P : ℝ) := by
  sorry
/-- States lem:gsound from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.certificate_sound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certificate_sound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (h N L : ℕ) (hcert : certificate c h N L) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States lem:gperiod from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.generic_tail_period in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem generic_tail_period (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n)
    (p : ℤ) (e m h N : ℕ) (hm : 0 < m) (hN : e ≤ N)
    (hdvd : m ∣ 2 ^ h - 1)
    (hS : binaryCoeffSeries c = (p : ℝ) / ((2 : ℝ) ^ e * m)) :
    binaryCoeffTail c (N + h) - binaryCoeffTail c N ∈ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States lem:gsound from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_difference in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaled_difference (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    (2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ) =
      binaryCoeffTail c (N + h + L) - binaryCoeffTail c (N + L) := by
  sorry
/-- States lem:gperiod from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.scaled_tail_split in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaled_tail_split (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (N L : ℕ) :
    (2 : ℝ) ^ L * binaryCoeffTail c N =
      (windowPrefix c N L : ℝ) + binaryCoeffTail c (N + L) := by
  sorry
/-- States lem:gsound from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.truncation_error_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem truncation_error_bound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) : := by
  sorry
end PalomarCorpus.E249.PaperStatementsAW
