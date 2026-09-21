/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.ActualForeignResidueProjection
import Erdos249257.ExponentOnlyTransport
import Erdos249257.FullTargetPrimeAdjunctionNoGo
import ErdosProblems.Erdos249.PaperCompleteR21.AffineDivisorAnnihilation
import ErdosProblems.Erdos249.PaperCompleteR21.PhaseEnergyAndForeignResidueProjection
import Solutions.PalomarCorpus.E249be.Statement

open scoped BigOperators
open scoped ArithmeticFunction.Moebius

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsBE

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

end PalomarCorpus.E249.PaperStatementsBE
