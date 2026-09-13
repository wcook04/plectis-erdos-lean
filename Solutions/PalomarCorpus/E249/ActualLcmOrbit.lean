/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos257PeriodNoncollapse.TotientActualLcmOrbitNonintegrality
import Solutions.PalomarCorpus.E249.Statement

open scoped BigOperators

namespace PalomarCorpus.E249.ActualLcmOrbit
export PalomarCorpus.E249.Shared (totientTail)

private theorem periodLcm_eq_source :
    ∀ t : ℕ, periodLcm t =
      Erdos257PeriodNoncollapse.TotientTailPeriodKiller.periodLcm t
  | 0 => rfl
  | t + 1 => by
      simp only [periodLcm,
        Erdos257PeriodNoncollapse.TotientTailPeriodKiller.periodLcm]
      rw [periodLcm_eq_source t]

theorem actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix (a : ℕ) :
    actualLcmTailOrbit a =
      (2 : ℝ) ^ actualLcmHeight a *
          ((2 : ℝ) ^ actualLcmHeight a - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) -
        ((totientPrefix (2 * actualLcmHeight a) : ℝ) -
          (totientPrefix (actualLcmHeight a) : ℝ)) := by
  simpa [actualLcmTailOrbit, actualLcmHeight, totientTail, totientPrefix,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientPrefix,
    periodLcm_eq_source] using
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix a

theorem irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      PowerTwoActualLcmOrbitNonintegralitySupply := by
  simpa [PowerTwoActualLcmOrbitNonintegralitySupply,
    actualLcmTailOrbit, actualLcmHeight, totientTail,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmOrbitNonintegralitySupply,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit,
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight,
    Erdos257PeriodNoncollapse.TotientTailPeriodKiller.totientTail,
    periodLcm_eq_source] using
    Erdos257PeriodNoncollapse.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply

end PalomarCorpus.E249.ActualLcmOrbit
