/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249be

Every non-theorem declaration of `PalomarCorpus/E249be/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace PalomarCorpus.E249.PaperStatementsBE
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
/-- The coefficient of the #249 constant in `R_(2H) - R_H`. Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.diagonalCoefficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalCoefficient (H : ℕ) : ℕ := 2 ^ H * (2 ^ H - 1)
/-- Closed geometric budget for every omitted channel when `2H ≤ D`. Local copy of Erdos249257.ActualForeignResidueProjection.foreignComplementBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def foreignComplementBound (H D : ℕ) : ℝ :=
  (diagonalCoefficient H : ℝ) *
    (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D))
/-- The least positive shift sending `N` to a multiple of `d`. Local copy of Erdos249257.ActualForeignResidueProjection.residueOffset, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def residueOffset (d N : ℕ) : ℕ := d - N % d
/-- The exact Möbius residue channel whose sum is the local totient tail. Local copy of Erdos249257.ActualForeignResidueProjection.foreignResidueKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def foreignResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - residueOffset d N) *
      (((N + residueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))
/-- Contribution of channel `d` to the diagonal `R_(2H) - R_H`. Local copy of Erdos249257.ActualForeignResidueProjection.residueIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def residueIncrement (d H : ℕ) : ℝ :=
  foreignResidueKernel d (2 * H) - foreignResidueKernel d H
/-- The actual foreign channels up to cutoff `D`; divisor channels are the explicit shadow and are deliberately excluded. Local copy of Erdos249257.ActualForeignResidueProjection.projectedForeignDefect, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def projectedForeignDefect (H D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ H then 0 else residueIncrement d H
/-- Least positive shift sending `N` to a multiple of `d`. Local copy of Erdos249257.ExponentOnlyTransport.transportResidueOffset, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def transportResidueOffset (d N : ℕ) : ℕ := d - N % d
/-- Exact Möbius residue kernel, stated locally so this disjoint transport owner can be validated independently of adjacent projection files. Local copy of Erdos249257.ExponentOnlyTransport.transportResidueKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def transportResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - transportResidueOffset d N) *
      (((N + transportResidueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))
/-- The manuscript's `K_d(N) = N/(d(2ᵈ-1)) + 2ᵈ/(2ᵈ-1)²`, the `d`th term of the Möbius expansion of `R_N` with its sign `μ(d)` removed. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusTermKernel (d N : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)) + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)
end PalomarCorpus.E249.PaperStatementsBE
