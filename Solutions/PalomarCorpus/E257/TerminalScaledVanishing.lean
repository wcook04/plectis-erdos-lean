/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos257.HalfCounterexampleFrontier
import Solutions.PalomarCorpus.E257.Statement

open Filter Set

namespace PalomarCorpus.E257.TerminalScaledVanishing
export PalomarCorpus.E257.Shared (UniversalMersenneSubseriesIrrationality erdosSupportSeries supportCoeff)

noncomputable section

private theorem affineBinaryOrbit_transport (a : ℕ → ℤ) (u0 : ℤ) (n : ℕ) :
    affineBinaryOrbit a u0 n = Erdos257PeriodNoncollapse.affineBinaryOrbit a u0 n := by
  induction n with
  | zero =>
      simp only [affineBinaryOrbit, Erdos257PeriodNoncollapse.affineBinaryOrbit]
  | succ n ih =>
      simp only [affineBinaryOrbit, Erdos257PeriodNoncollapse.affineBinaryOrbit, ih]

private theorem integerHalfCarry_transport (A : Set ℕ) (n : ℕ) :
    integerHalfCarry A n =
      Erdos257PeriodNoncollapse.HalfCarryReachability.integerHalfCarry A n := by
  simp only [integerHalfCarry,
    Erdos257PeriodNoncollapse.HalfCarryReachability.integerHalfCarry,
    affineBinaryOrbit_transport,
    show supportCoeff = Erdos257PeriodNoncollapse.supportCoeff from rfl]

private theorem wordSupport_transport {N : ℕ} (a : HalfWord N) :
    wordSupport a = Erdos257PeriodNoncollapse.HalfCarryReachability.wordSupport a := rfl

theorem terminalScaledVanishing_completeCounterexample
    (S : HalfTerminalOnlyScaledVanishingSequence) :
    (∃ A : Set ℕ, A.Infinite ∧
      erdosSupportSeries 2 A = (1 : ℝ) / 2) ∧
    ¬ UniversalMersenneSubseriesIrrationality := by
  let S' :
      Erdos257PeriodNoncollapse.HalfCarryReachability.HalfTerminalOnlyScaledVanishingSequence :=
    { depth := S.depth
      word := S.word
      depth_pos := S.depth_pos
      depth_tendsto := S.depth_tendsto
      zero := S.zero
      one := S.one
      carry_scaled_tendsto := by
        simpa only [integerHalfCarry_transport, wordSupport_transport] using
          S.carry_scaled_tendsto }
  rw [show erdosSupportSeries = Erdos257PeriodNoncollapse.erdosSupportSeries from rfl,
    show UniversalMersenneSubseriesIrrationality =
      ErdosProblems.Erdos257.UniversalMersenneSubseriesIrrationality from rfl]
  exact
    ⟨ErdosProblems.Erdos257.exists_rational_half_counterexample_of_terminalScaledVanishing S',
      ErdosProblems.Erdos257.not_universal_of_terminalScaledVanishing S'⟩

end

end PalomarCorpus.E257.TerminalScaledVanishing
