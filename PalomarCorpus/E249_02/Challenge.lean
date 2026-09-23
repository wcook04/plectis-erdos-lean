/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record sections 1 to 2: totient sections and tail differences; rational comparison sequences

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Filter
open scoped BigOperators
open Set

namespace PalomarCorpus.E249_02.Shared
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.discrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def discrepancy (c : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((c (N + h + j + 1) : ℤ) - c (N + j + 1)) * 2 ^ (L - 1 - j)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates.certificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certificate (c : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < discrepancy c h N L % 2 ^ L ∧
  discrepancy c h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.dyadicBase, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicBase (B : ℕ) : ℚ :=
  2 - ∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℚ) / 2 ^ n
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def gamma (B P n : ℕ) : ℕ :=
  if n ≤ B then Nat.totient n else if P ∣ n then n - 1 else n
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.value, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def value (B P : ℕ) : ℚ := dyadicBase B - 1 / ((2 ^ P - 1 : ℕ) : ℚ)
end PalomarCorpus.E249_02.Shared

namespace PalomarCorpus.E249.PaperStatementsAG
open Filter
/-- Lacunary spike ranks `2^(k+3)`, beginning at `8`. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.IsLargePowerTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsLargePowerTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 ^ (k + 3)
/-- The zero-one indicator of the lacunary spike ranks. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.largePowerTwoBit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def largePowerTwoBit (n : ℕ) : ℕ := by
  classical
  exact if IsLargePowerTwo n then 1 else 0
/-- Rational base coefficients before adding zero-valued sparse carries. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.parityBaseWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def parityBaseWeight : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 4
/-- The parity countermodel. Natural subtraction is exact because every negative spike lands on a base coefficient `4`. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def parityCoboundaryWeight (n : ℕ) : ℕ :=
  parityBaseWeight n + 2 * largePowerTwoBit n -
    4 * largePowerTwoBit (n - 1)
/-- States prop:parity from the long record for Erdős problem #249. Transported from Erdos249257.TotientParityCoboundaryCountermodel.tsum_parityCoboundaryWeight_eq_three_halves in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_parityCoboundaryWeight_eq_three_halves :
    (∑' n : ℕ, (parityCoboundaryWeight n : ℝ) / 2 ^ n) = 3 / 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAG

namespace PalomarCorpus.E249.PaperStatementsAW
open scoped BigOperators
open Filter
open Set
export PalomarCorpus.E249_02.Shared (certificate discrepancy dyadicBase gamma value)
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The scaled tail `T_c(N) = ∑_{j≥1} c(N+j)/2^j`. Local copy of Erdos249257.binaryCoeffTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)
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
theorem truncation_error_bound (c : ℕ → ℕ) (hc : ∀ n, c n ≤ n) (h N L : ℕ) :
    |(2 : ℝ) ^ L * (binaryCoeffTail c (N + h) - binaryCoeffTail c N) -
      (discrepancy c h N L : ℝ)| ≤ (N : ℝ) + h + L + 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAW

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_02.Shared (certificate discrepancy dyadicBase gamma value)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.separation, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def separation (c : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certificate c h N L
/-- States thm:gamma from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.discrepancy_prefix in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem discrepancy_prefix (B P h N L : ℕ) (hB : N + h + L ≤ B) :
    discrepancy (gamma B P) h N L =
      discrepancy Nat.totient h N L := by
  sorry
/-- States thm:gamma from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_denominator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exact_denominator (B P : ℕ) (hBP : B < P) :
    ∃ e ≤ B, (value B P).den = 2 ^ e * (2 ^ P - 1) := by
  sorry
/-- States thm:gamma from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gamma_le (B P n : ℕ) : gamma B P n ≤ n := by
  sorry
/-- States cor:b1, thm:gamma from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_not_separation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gamma_not_separation (B P : ℕ) (hBP : B < P) : ¬ separation (gamma B P) := by
  sorry
/-- States thm:gamma from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_prefix in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gamma_prefix (B P n : ℕ) (hn : n ≤ B) : gamma B P n = Nat.totient n := by
  sorry
/-- States thm:gamma from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_certificate_after_prefix in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_certificate_after_prefix (B P : ℕ) (hBP : B < P) :
    ∀ N : ℕ, B ≤ N → ∀ L : ℕ, ¬ certificate (gamma B P) P N L := by
  sorry
/-- States cor:b1 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_uniform_prefix_rule in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem no_uniform_prefix_rule (B : ℕ) :
    ¬ (∀ c : ℕ → ℕ, (∀ n, c n ≤ n) → (∀ n, n ≤ B → c n = Nat.totient n) → separation c) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAE
