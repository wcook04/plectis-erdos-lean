/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_18

Every non-theorem declaration of `PalomarCorpus/E249_18/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open scoped Polynomial
open Finset
open scoped ArithmeticFunction.Moebius

namespace PalomarCorpus.E249_18.Shared
/-- The coefficient of the #249 constant in `R_(2H) - R_H`. Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.diagonalCoefficient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalCoefficient (H : ℕ) : ℕ := 2 ^ H * (2 ^ H - 1)
/-- Closed geometric budget for every omitted channel when `2H ≤ D`. Local copy of Erdos249257.ActualForeignResidueProjection.foreignComplementBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def foreignComplementBound (H D : ℕ) : ℝ :=
  (diagonalCoefficient H : ℝ) *
    (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D))
/-- The Mersenne denominator at exponent `n`. Local copy of Erdos249257.RadicalMobiusShadow.mersenne, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1
/-- The integral numerator, written as its squarefree-divisor expansion. For `s ⊆ primeFactors(r)`, put `d = ∏ p ∈ s, p`. Then the summand is `(-1)^|s| (r/d) ((2^r-1)/(2^d-1))`. This is exactly the nonzero part of `Σ_{d ∣ r} μ(d) (r/d) ((2^r-1)/(2^d-1))`: nonsquarefree divisors have Möbius coefficient zero. The subset form makes that finite support explicit and keeps the definition executable without factoring irrelevant divisors. Local copy of Erdos249257.RadicalMobiusShadow.mobiusNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)
/-- The unscaled radical shadow `B(r) = M_r / (2^r - 1)`. Local copy of Erdos249257.RadicalMobiusShadow.baseMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)
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
/-- The squarefree kernel used by the numeric shadow: the product of the distinct prime factors of `n`. For `n = 0` this convention gives `1`; all development-facing scaling theorems assume `0 < n`. Local copy of Erdos249257.RadicalMobiusShadow.squarefreeKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p
/-- The numeric shadow at an arbitrary scale. By construction it only sees the distinct prime factors of `H`. Local copy of Erdos249257.RadicalMobiusShadow.numericMobiusShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)
/-- The exact rational explicit shadow at an arbitrary scale. Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.scaleExplicitShadowRat, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scaleExplicitShadowRat (H : ℕ) : ℚ :=
  (H : ℚ) * numericMobiusShadow H
/-- Local copy of Erdos249257.FullTargetPrimeAdjunctionNoGo.scaleExplicitShadow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scaleExplicitShadow (H : ℕ) : ℝ :=
  (scaleExplicitShadowRat H : ℝ)
end PalomarCorpus.E249_18.Shared

namespace PalomarCorpus.E249.PaperStatementsAO
open scoped BigOperators
open scoped Polynomial
/-- The paper's numerator polynomial `∑_{d ∣ r} μ(d)(r/d) ∑_{j<r/d} X^{dj}`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.paperNumeratorPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperNumeratorPolynomial (r : ℕ) : Polynomial ℤ :=
  ∑ d ∈ r.divisors,
    Polynomial.C (ArithmeticFunction.moebius d * ((r / d : ℕ) : ℤ)) *
      ∑ j ∈ Finset.range (r / d), (Polynomial.X : Polynomial ℤ) ^ (d * j)
end PalomarCorpus.E249.PaperStatementsAO

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
export PalomarCorpus.E249_18.Shared (baseMobiusShadow mersenne mobiusNumerator numericMobiusShadow scaleExplicitShadow scaleExplicitShadowRat squarefreeKernel)
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsBE
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
export PalomarCorpus.E249_18.Shared (diagonalCoefficient foreignComplementBound foreignResidueKernel projectedForeignDefect residueIncrement residueOffset)
end PalomarCorpus.E249.PaperStatementsBE

namespace PalomarCorpus.E249.PaperStatementsBK
open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open Finset
export PalomarCorpus.E249_18.Shared (baseMobiusShadow diagonalCoefficient foreignComplementBound foreignResidueKernel mersenne mobiusNumerator numericMobiusShadow projectedForeignDefect residueIncrement residueOffset scaleExplicitShadow scaleExplicitShadowRat squarefreeKernel)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249.PaperStatementsBK

namespace PalomarCorpus.E249.PaperStatementsAJ
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAK
end PalomarCorpus.E249.PaperStatementsAK
