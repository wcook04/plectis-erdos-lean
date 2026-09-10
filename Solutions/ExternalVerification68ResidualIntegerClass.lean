/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.PaperCompleteResidualIdentity

/-!
# Source transport for the Erdős #68 full residual integer class

The declarations below restate the Mathlib-only challenge vocabulary and
transport the exact source theorems without strengthening their hypotheses.
-/

namespace Erdos249257.ExternalVerification68ResidualIntegerClass

open scoped BigOperators
open Finsupp

def channelWeight (i d : ℕ) : ℕ :=
  i.factorial / (d.factorial ^ (i / d))

def channelNumerator (lam : ℕ →₀ ℤ) (d : ℕ) : ℤ :=
  lam.sum fun i z => z * (channelWeight i d : ℤ)

def factorialMoment (lam : ℕ →₀ ℤ) : ℤ :=
  lam.sum fun i z => z * (i.factorial : ℤ)

def channelLCM (D : ℕ) : ℕ :=
  (Finset.Icc 2 D).lcm (fun d => d.factorial - 1)

noncomputable def adjacentDifference (n : ℕ) : ℕ →₀ ℤ :=
  single (n - 1) (n : ℤ) - single n 1

noncomputable def isolatedChannelUnit (n : ℕ) : ℕ →₀ ℤ :=
  n.strongRecOn' fun n rec =>
    if n ≤ 1 then 0
    else
      adjacentDifference n -
        ∑ d ∈ (Finset.Ico 2 n).attach,
          if d.1 ∣ n then
            (channelWeight n d.1 : ℤ) • rec d.1 (Finset.mem_Ico.mp d.2).2
          else 0

noncomputable def channelBasisColumn (j : ℕ) : ℕ →₀ ℤ :=
  if j = 0 then single 1 1 else isolatedChannelUnit (j + 1)

noncomputable def channelSynthesis (a : ℕ →₀ ℤ) : ℕ →₀ ℤ :=
  a.sum (fun j z => z • channelBasisColumn j)

noncomputable def kernelCoordinates (D : ℕ) : ℕ →₀ ℤ :=
  single 0 (channelLCM D : ℤ) -
    ∑ d ∈ Finset.Icc 2 D,
      single (d - 1) ((channelLCM D : ℤ) / ((d.factorial : ℤ) - 1))

noncomputable def canonicalKernel (D : ℕ) : ℕ →₀ ℤ :=
  channelSynthesis (kernelCoordinates D)

def TailCoordinates (D : ℕ) (z : ℕ →₀ ℤ) : Prop :=
  ∀ j, j < D → z j = 0

noncomputable def integerEvaluation (w : ℕ → ℤ) (z : ℕ →₀ ℤ) : ℤ :=
  z.sum (fun i c => c * w i)

noncomputable def coordinateMass (z : ℕ →₀ ℤ) : ℤ :=
  integerEvaluation (fun _ => 1) z

noncomputable def fullResidualTerm (f : ℕ →₀ ℤ) (d : ℕ) : ℝ :=
  if 1 < d then (channelNumerator f d : ℝ) /
    ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ) else 0

noncomputable def fullResidual (f : ℕ →₀ ℤ) : ℝ :=
  ∑' d : ℕ, fullResidualTerm f d

noncomputable def gapPrefixReal (D : ℕ) : ℝ :=
  ∑ d ∈ Finset.Icc 2 D, (1 : ℝ) / ((((d.factorial : ℤ) - 1 : ℤ)) : ℝ)

noncomputable def factorialGapSeries : ℝ :=
  ∑' n : ℕ, if 1 < n then (1 : ℝ) / (((n.factorial : ℤ) - 1 : ℤ) : ℝ) else 0

theorem residual_transparency {D : ℕ} (hD : 2 ≤ D) (t : ℤ)
    {z : ℕ →₀ ℤ} (hz : TailCoordinates D z) :
    fullResidual (t • canonicalKernel D + channelSynthesis z) =
      (t : ℝ) * (channelLCM D : ℝ) *
        (factorialGapSeries - gapPrefixReal D) +
      (coordinateMass z : ℝ) := by
  simpa [channelWeight, channelNumerator, factorialMoment, channelLCM,
    adjacentDifference, isolatedChannelUnit, channelBasisColumn, channelSynthesis,
    kernelCoordinates, canonicalKernel, TailCoordinates, integerEvaluation,
    coordinateMass, fullResidualTerm, fullResidual, gapPrefixReal,
    factorialGapSeries, ErdosProblems.Erdos68.channelWeight,
    ErdosProblems.Erdos68.channelNumerator, ErdosProblems.Erdos68.factorialMoment,
    ErdosProblems.Erdos68.channelLCM, ErdosProblems.Erdos68.adjacentDifference,
    ErdosProblems.Erdos68.isolatedChannelUnit,
    ErdosProblems.Erdos68.PaperComplete.channelBasisColumn,
    ErdosProblems.Erdos68.PaperComplete.channelSynthesis,
    ErdosProblems.Erdos68.PaperComplete.kernelCoordinates,
    ErdosProblems.Erdos68.PaperComplete.canonicalKernel,
    ErdosProblems.Erdos68.PaperComplete.TailCoordinates,
    ErdosProblems.Erdos68.PaperComplete.integerEvaluation,
    ErdosProblems.Erdos68.PaperComplete.coordinateMass,
    ErdosProblems.Erdos68.PaperComplete.fullResidualTerm,
    ErdosProblems.Erdos68.PaperComplete.fullResidual,
    ErdosProblems.Erdos68.PaperComplete.gapPrefixReal, Erdos68.factorialGapSeries,
    Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm] using
    ErdosProblems.Erdos68.PaperComplete.residual_transparency hD t hz

theorem summable_fullResidual {f : ℕ →₀ ℤ} (h0 : f 0 = 0) :
    Summable (fullResidualTerm f) := by
  simpa [channelWeight, channelNumerator, factorialMoment, channelLCM,
    adjacentDifference, isolatedChannelUnit, channelBasisColumn, channelSynthesis,
    kernelCoordinates, canonicalKernel, TailCoordinates, integerEvaluation,
    coordinateMass, fullResidualTerm, fullResidual, gapPrefixReal,
    factorialGapSeries, ErdosProblems.Erdos68.channelWeight,
    ErdosProblems.Erdos68.channelNumerator, ErdosProblems.Erdos68.factorialMoment,
    ErdosProblems.Erdos68.channelLCM, ErdosProblems.Erdos68.adjacentDifference,
    ErdosProblems.Erdos68.isolatedChannelUnit,
    ErdosProblems.Erdos68.PaperComplete.channelBasisColumn,
    ErdosProblems.Erdos68.PaperComplete.channelSynthesis,
    ErdosProblems.Erdos68.PaperComplete.kernelCoordinates,
    ErdosProblems.Erdos68.PaperComplete.canonicalKernel,
    ErdosProblems.Erdos68.PaperComplete.TailCoordinates,
    ErdosProblems.Erdos68.PaperComplete.integerEvaluation,
    ErdosProblems.Erdos68.PaperComplete.coordinateMass,
    ErdosProblems.Erdos68.PaperComplete.fullResidualTerm,
    ErdosProblems.Erdos68.PaperComplete.fullResidual,
    ErdosProblems.Erdos68.PaperComplete.gapPrefixReal, Erdos68.factorialGapSeries,
    Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm] using
    ErdosProblems.Erdos68.PaperComplete.summable_fullResidual h0

theorem zero_moment_residual_integral {f : ℕ →₀ ℤ}
    (h0 : f 0 = 0) (hm : factorialMoment f = 0) :
    ∃ k : ℤ, fullResidual f = (k : ℝ) := by
  simpa [channelWeight, channelNumerator, factorialMoment, channelLCM,
    adjacentDifference, isolatedChannelUnit, channelBasisColumn, channelSynthesis,
    kernelCoordinates, canonicalKernel, TailCoordinates, integerEvaluation,
    coordinateMass, fullResidualTerm, fullResidual, gapPrefixReal,
    factorialGapSeries, ErdosProblems.Erdos68.channelWeight,
    ErdosProblems.Erdos68.channelNumerator, ErdosProblems.Erdos68.factorialMoment,
    ErdosProblems.Erdos68.channelLCM, ErdosProblems.Erdos68.adjacentDifference,
    ErdosProblems.Erdos68.isolatedChannelUnit,
    ErdosProblems.Erdos68.PaperComplete.channelBasisColumn,
    ErdosProblems.Erdos68.PaperComplete.channelSynthesis,
    ErdosProblems.Erdos68.PaperComplete.kernelCoordinates,
    ErdosProblems.Erdos68.PaperComplete.canonicalKernel,
    ErdosProblems.Erdos68.PaperComplete.TailCoordinates,
    ErdosProblems.Erdos68.PaperComplete.integerEvaluation,
    ErdosProblems.Erdos68.PaperComplete.coordinateMass,
    ErdosProblems.Erdos68.PaperComplete.fullResidualTerm,
    ErdosProblems.Erdos68.PaperComplete.fullResidual,
    ErdosProblems.Erdos68.PaperComplete.gapPrefixReal, Erdos68.factorialGapSeries,
    Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm] using
    ErdosProblems.Erdos68.PaperComplete.zero_moment_residual_integral h0 hm

theorem equal_moment_residual_integer_difference {f g : ℕ →₀ ℤ}
    (hf0 : f 0 = 0) (hg0 : g 0 = 0) (hm : factorialMoment f = factorialMoment g) :
    ∃ k : ℤ, fullResidual f - fullResidual g = (k : ℝ) := by
  simpa [channelWeight, channelNumerator, factorialMoment, channelLCM,
    adjacentDifference, isolatedChannelUnit, channelBasisColumn, channelSynthesis,
    kernelCoordinates, canonicalKernel, TailCoordinates, integerEvaluation,
    coordinateMass, fullResidualTerm, fullResidual, gapPrefixReal,
    factorialGapSeries, ErdosProblems.Erdos68.channelWeight,
    ErdosProblems.Erdos68.channelNumerator, ErdosProblems.Erdos68.factorialMoment,
    ErdosProblems.Erdos68.channelLCM, ErdosProblems.Erdos68.adjacentDifference,
    ErdosProblems.Erdos68.isolatedChannelUnit,
    ErdosProblems.Erdos68.PaperComplete.channelBasisColumn,
    ErdosProblems.Erdos68.PaperComplete.channelSynthesis,
    ErdosProblems.Erdos68.PaperComplete.kernelCoordinates,
    ErdosProblems.Erdos68.PaperComplete.canonicalKernel,
    ErdosProblems.Erdos68.PaperComplete.TailCoordinates,
    ErdosProblems.Erdos68.PaperComplete.integerEvaluation,
    ErdosProblems.Erdos68.PaperComplete.coordinateMass,
    ErdosProblems.Erdos68.PaperComplete.fullResidualTerm,
    ErdosProblems.Erdos68.PaperComplete.fullResidual,
    ErdosProblems.Erdos68.PaperComplete.gapPrefixReal, Erdos68.factorialGapSeries,
    Erdos68.factorialGapTail, Erdos68.factorialGapTailTerm] using
    ErdosProblems.Erdos68.PaperComplete.equal_moment_residual_integer_difference
      hf0 hg0 hm

end Erdos249257.ExternalVerification68ResidualIntegerClass
