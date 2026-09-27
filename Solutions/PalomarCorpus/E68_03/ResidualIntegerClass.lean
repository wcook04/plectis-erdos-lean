/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PaperCompleteResidualIdentity
import Solutions.PalomarCorpus.E68_03.Statement

open scoped BigOperators
open Finsupp

namespace PalomarCorpus.E68.ResidualIntegerClass
export PalomarCorpus.E68_03.Shared (channelLCM)

theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ) := by
  exact ErdosProblems.Erdos68.PaperComplete.residual_transparency hD t hz

theorem summable_fullResidual {f : ℕ →₀ ℤ} (h0 : f 0 = 0) :
    Summable (fullResidualTerm f) := by
  exact ErdosProblems.Erdos68.PaperComplete.summable_fullResidual h0

theorem zero_moment_residual_integral {f : ℕ →₀ ℤ}
    (h0 : f 0 = 0) (hm : factorialMoment f = 0) :
    ∃ k : ℤ, fullResidual f = (k : ℝ) := by
  exact ErdosProblems.Erdos68.PaperComplete.zero_moment_residual_integral h0 hm

theorem equal_moment_residual_integer_difference {f g : ℕ →₀ ℤ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hm : factorialMoment f = factorialMoment g) :
    ∃ k : ℤ, fullResidual f - fullResidual g = (k : ℝ) := by
  exact ErdosProblems.Erdos68.PaperComplete.equal_moment_residual_integer_difference hf0 hg0 hm

end PalomarCorpus.E68.ResidualIntegerClass
