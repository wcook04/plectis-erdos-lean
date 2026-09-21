/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band e

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
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
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.divisorChannels_sum_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem divisorChannels_sum_eq (H : ℕ) (_hH : 0 < H) :
    ∑ d ∈ H.divisors, residueIncrement d H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.foreignComplementBound_paper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem foreignComplementBound_paper (H D : ℕ) :
    foreignComplementBound H D =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.projectedForeignDefect_paper in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem projectedForeignDefect_paper (H D : ℕ) :
    projectedForeignDefect H D =
      ∑ d ∈ Finset.Icc 1 D,
        (if d ∣ H then 0
          else foreignResidueKernel d (2 * H) - foreignResidueKernel d H) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.residueKernel_increment_of_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem residueKernel_increment_of_dvd {d H : ℕ} (hd : 0 < d) (hdvd : d ∣ H) :
    foreignResidueKernel d (2 * H) - foreignResidueKernel d H =
      (H : ℝ) * ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.residueOffset_of_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem residueOffset_of_dvd {d H : ℕ} (_hd : 0 < d) (hdvd : d ∣ H) :
    residueOffset d H = d ∧ residueOffset d (2 * H) = d := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.transportResidueKernel_eq_mobiusTermKernel in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem transportResidueKernel_eq_mobiusTermKernel {d N : ℕ}
    (hd : 0 < d) (hdN : d ∣ N) :
    transportResidueKernel d N
      = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * mobiusTermKernel d N := by
  sorry
end PalomarCorpus.E249.PaperStatementsBE
