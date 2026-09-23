/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_02

Every non-theorem declaration of `PalomarCorpus/E249_02/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E249.PaperStatementsAW

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_02.Shared (certificate discrepancy dyadicBase gamma value)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.separation, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def separation (c : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certificate c h N L
end PalomarCorpus.E249.PaperStatementsAE
