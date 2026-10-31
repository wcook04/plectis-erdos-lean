/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos257.HalfCounterexampleFrontier

namespace Erdos249257.ExternalVerification257TerminalScaledVanishing

open Filter Set

noncomputable section

noncomputable def supportCoeff (A : Set ℕ) (n : ℕ) : ℕ :=
  letI := Classical.decPred fun d : ℕ => d ∈ A
  (n.divisors.filter fun d => d ∈ A).card

noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)

noncomputable def integerHalfCarry (A : Set ℕ) : ℕ → ℤ :=
  affineBinaryOrbit (fun n : ℕ ↦ (supportCoeff A (n + 1) : ℤ)) 1

noncomputable abbrev HalfWord (N : ℕ) := Fin (N + 1) → Bool

noncomputable def wordSupport {N : ℕ} (a : HalfWord N) : Set ℕ :=
  {n | ∃ h : n < N + 1, a ⟨n, h⟩ = true}

structure HalfTerminalOnlyScaledVanishingSequence where
  depth : ℕ → ℕ
  word : ∀ n : ℕ, HalfWord (depth n)
  depth_pos : ∀ n : ℕ, 1 ≤ depth n
  depth_tendsto : Tendsto depth atTop atTop
  zero : ∀ n : ℕ,
    word n ⟨0, Nat.zero_lt_succ (depth n)⟩ = false
  one : ∀ (n : ℕ) (h : 1 < depth n + 1), word n ⟨1, h⟩ = false
  carry_scaled_tendsto :
    Tendsto
      (fun n : ℕ ↦
        |(integerHalfCarry (wordSupport (word n)) (depth n - 1) : ℝ)| /
          (2 : ℝ) ^ depth n)
      atTop (nhds 0)

noncomputable def erdosSupportSeries (b : ℕ) (A : Set ℕ) : ℝ :=
  ∑' a : ℕ, Set.indicator A
    (fun a => (1 : ℝ) / ((b : ℝ) ^ a - 1)) a

noncomputable def UniversalMersenneSubseriesIrrationality : Prop :=
  ∀ A : Set ℕ, A.Infinite → Irrational (erdosSupportSeries 2 A)

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

end Erdos249257.ExternalVerification257TerminalScaledVanishing
