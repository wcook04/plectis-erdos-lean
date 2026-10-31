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
`Erdos249257.ActualForeignResidueProjection`, `Erdos249257.FullTargetPrimeAdjunctionNoGo`,
`Erdos249257.RadicalMobiusShadow`, `Erdos249257.TotientTailPeriodKiller`,
`ErdosProblems.Erdos249.PaperCompleteR21.PhaseEnergyAndForeignResidueProjection`.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius
open Finset

namespace Erdos249257.ExternalVerification249PaperStatementsBK

noncomputable def diagonalCoefficient (H : ℕ) : ℕ := 2 ^ H * (2 ^ H - 1)

noncomputable def foreignComplementBound (H D : ℕ) : ℝ :=
  (diagonalCoefficient H : ℝ) *
    (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D))

noncomputable def residueOffset (d N : ℕ) : ℕ := d - N % d

noncomputable def foreignResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - residueOffset d N) *
      (((N + residueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))

noncomputable def residueIncrement (d H : ℕ) : ℝ :=
  foreignResidueKernel d (2 * H) - foreignResidueKernel d H

noncomputable def projectedForeignDefect (H D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 1 D, if d ∣ H then 0 else residueIncrement d H

noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)

noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)

noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)

noncomputable def scaleExplicitShadowRat (H : ℕ) : ℚ :=
  (H : ℚ) * numericMobiusShadow H

noncomputable def scaleExplicitShadow (H : ℕ) : ℝ :=
  (scaleExplicitShadowRat H : ℝ)

noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_not_integral_of_separation in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tailDifference_not_integral_of_separation {H D : ℕ}
    (hbound :
      |totientTail (2 * H) - totientTail H -
        (scaleExplicitShadow H + projectedForeignDefect H D)| ≤
        foreignComplementBound H D)
    (hsep : ∀ z : ℤ,
      foreignComplementBound H D <
        |scaleExplicitShadow H + projectedForeignDefect H D - (z : ℝ)|) :
    totientTail (2 * H) - totientTail H ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsBK
