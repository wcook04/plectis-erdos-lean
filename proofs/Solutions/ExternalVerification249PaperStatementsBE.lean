/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.ActualForeignResidueProjection
import Erdos249257.ExponentOnlyTransport
import Erdos249257.FullTargetPrimeAdjunctionNoGo
import ErdosProblems.Erdos249.PaperCompleteR21.AffineDivisorAnnihilation
import ErdosProblems.Erdos249.PaperCompleteR21.PhaseEnergyAndForeignResidueProjection

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.ActualForeignResidueProjection`, `Erdos249257.ExponentOnlyTransport`,
`Erdos249257.FullTargetPrimeAdjunctionNoGo`,
`ErdosProblems.Erdos249.PaperCompleteR21.AffineDivisorAnnihilation`,
`ErdosProblems.Erdos249.PaperCompleteR21.PhaseEnergyAndForeignResidueProjection`.
-/

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

namespace Erdos249257.ExternalVerification249PaperStatementsBE

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

noncomputable def transportResidueOffset (d N : ℕ) : ℕ := d - N % d

noncomputable def transportResidueKernel (d N : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ) *
    (2 : ℝ) ^ (d - transportResidueOffset d N) *
      (((N + transportResidueOffset d N : ℕ) : ℝ) /
          ((d : ℝ) * ((2 : ℝ) ^ d - 1)) +
        1 / (((2 : ℝ) ^ d - 1) ^ 2))

noncomputable def mobiusTermKernel (d N : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)) + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)

theorem divisorChannels_sum_eq (H : ℕ) (_hH : 0 < H) :
    ∑ d ∈ H.divisors, residueIncrement d H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := @ErdosProblems.Erdos249.PaperCompleteR21.divisorChannels_sum_eq H _hH

theorem foreignComplementBound_paper (H D : ℕ) :
    foreignComplementBound H D =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        (2 / (2 : ℝ) ^ D + 4 / (3 * (4 : ℝ) ^ D)) := @ErdosProblems.Erdos249.PaperCompleteR21.foreignComplementBound_paper H D

theorem projectedForeignDefect_paper (H D : ℕ) :
    projectedForeignDefect H D =
      ∑ d ∈ Finset.Icc 1 D,
        (if d ∣ H then 0
          else foreignResidueKernel d (2 * H) - foreignResidueKernel d H) := @ErdosProblems.Erdos249.PaperCompleteR21.projectedForeignDefect_paper H D

theorem residueKernel_increment_of_dvd {d H : ℕ} (hd : 0 < d) (hdvd : d ∣ H) :
    foreignResidueKernel d (2 * H) - foreignResidueKernel d H =
      (H : ℝ) * ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
        ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := @ErdosProblems.Erdos249.PaperCompleteR21.residueKernel_increment_of_dvd d H hd hdvd

theorem residueOffset_of_dvd {d H : ℕ} (_hd : 0 < d) (hdvd : d ∣ H) :
    residueOffset d H = d ∧ residueOffset d (2 * H) = d := @ErdosProblems.Erdos249.PaperCompleteR21.residueOffset_of_dvd d H _hd hdvd

theorem transportResidueKernel_eq_mobiusTermKernel {d N : ℕ}
    (hd : 0 < d) (hdN : d ∣ N) :
    transportResidueKernel d N
      = ((ArithmeticFunction.moebius d : ℤ) : ℝ) * mobiusTermKernel d N := @ErdosProblems.Erdos249.PaperCompleteR21.transportResidueKernel_eq_mobiusTermKernel d N hd hdN

end Erdos249257.ExternalVerification249PaperStatementsBE
