/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243_03

Every non-theorem declaration of `PalomarCorpus/E243_03/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter Topology
open scoped BigOperators
open Filter
open scoped Topology
open Asymptotics

namespace PalomarCorpus.E243_03.Shared
/-- The centred reciprocal-tail error `D - (a - 1) * C` of an integer state, the integer measuring the failure of the identity `D = (a - 1) * C` that holds exactly on a Sylvester tail. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- The prefix product `a 0 * a 1 * ... * a (n-1)` of the first `n` terms of a natural sequence, with the empty product `1` at `n = 0`. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- The denominator q multiplied by the product of the first n terms of a. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- The integer numerator obtained by clearing q times the prefix product from the first n terms of the reciprocal-series remainder. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- The natural-number projection of the cleared integer remainder numerator. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- The truncated base-two iterated logarithm log₂(log₂(max(4, x))). -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2
/-- The nonnegative part of the negative error, divided by the truncated iterated logarithm of the numerator. -/
noncomputable def negativeErrorLogLogCharge (U : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  ((max (-E n) 0 : ℤ) : ℝ) / recordLogLog (U n)
/-- The Sylvester successor `a² - a + 1`, expressed in a ring. Local copy of ErdosProblems.Erdos243.sylvesterNext, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1
end PalomarCorpus.E243_03.Shared

namespace PalomarCorpus.E243.CompletePaperRecords
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E243_03.Shared (canonicalDenominator canonicalNaturalNumerator centeredState clearedIntegerNumerator negativeErrorLogLogCharge prefixProduct recordLogLog sylvesterNext)
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The increment of the running maximum divided by the truncated iterated logarithm of its preceding value. -/
noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)
/-- The extended-real limit superior of the normalized running-record increments. -/
noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop
end PalomarCorpus.E243.CompletePaperRecords

namespace PalomarCorpus.E243.PaperStatementsM
open Filter
open scoped Topology
open scoped BigOperators
export PalomarCorpus.E243_03.Shared (canonicalNaturalNumerator clearedIntegerNumerator prefixProduct recordLogLog sylvesterNext)
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The increment of the running maximum divided by the truncated iterated logarithm of its preceding value. -/
noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)
/-- The extended-real limit superior of the normalized running-record increments. -/
noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop
end PalomarCorpus.E243.PaperStatementsM

namespace PalomarCorpus.E243.PaperStatementsI
open Filter
open scoped Topology
open scoped BigOperators
export PalomarCorpus.E243_03.Shared (canonicalDenominator canonicalNaturalNumerator centeredState clearedIntegerNumerator negativeErrorLogLogCharge prefixProduct recordLogLog sylvesterNext)
end PalomarCorpus.E243.PaperStatementsI

namespace PalomarCorpus.E243.PaperStructuresT
open Filter
open Asymptotics
open scoped BigOperators
open scoped Topology
export PalomarCorpus.E243_03.Shared (canonicalDenominator canonicalNaturalNumerator clearedIntegerNumerator prefixProduct)
/-- **The standing hypotheses of §`long243:sec:records`.** These are exactly the hypotheses of Problem `long243:res:problem`: a strictly increasing sequence of positive integers with `a (n+1) / a n ^ 2 → 1` and rational reciprocal sum, presented by an explicit integer numerator `num` and positive natural denominator `den`. The section's integer tails are the canonical ones constructed from this data; they are definitions below, not further hypotheses. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit, restated so the compared statements elaborate against Mathlib alone. -/
structure StandingOrbit where
  a : ℕ → ℕ
  num : ℤ
  den : ℕ
  a_strictMono : StrictMono a
  a_pos : ∀ n, 0 < a n
  den_pos : 0 < den
  hasSum : HasSum (fun n ↦ 1 / (a n : ℝ)) ((num : ℝ) / (den : ℝ))
  growth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)
/-- Local definition C, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.C (O : StandingOrbit) : ℕ → ℕ := canonicalNaturalNumerator O.a O.num O.den
/-- Local definition D, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.D (O : StandingOrbit) : ℕ → ℕ := canonicalDenominator O.a O.den
/-- Local definition EventuallySylvester, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.EventuallySylvester (O : StandingOrbit) : Prop :=
  ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1
/-- Local definition G, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.G (O : StandingOrbit) (n : ℕ) : ℕ := Nat.gcd (O.C n) (O.D n)
/-- Local definition u, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.u (O : StandingOrbit) (n : ℕ) : ℕ := O.C n / O.G n
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- Local definition R, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.R (O : StandingOrbit) : ℕ → ℕ := runningMax O.u
/-- Local definition v, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.v (O : StandingOrbit) (n : ℕ) : ℕ := O.D n / O.G n
/-- Local definition redErr, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.redErr (O : StandingOrbit) (n : ℕ) : ℤ := (O.v n : ℤ) - ((O.a n : ℤ) - 1) * (O.u n : ℤ)
/-- Local definition negPart, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.negPart (O : StandingOrbit) (n : ℕ) : ℕ := (-O.redErr n).toNat
/-- Local definition amp, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.amp (O : StandingOrbit) (n : ℕ) : ℝ := (O.R n : ℝ) * (O.negPart n : ℝ) / (O.u n : ℝ)
/-- Local definition canc, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.canc (O : StandingOrbit) (n : ℕ) : ℕ := O.G (n + 1) / O.G n
/-- Local definition delta, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.delta (O : StandingOrbit) (n : ℕ) : ℝ :=
  max 0 ((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)
end PalomarCorpus.E243.PaperStructuresT

namespace PalomarCorpus.E243.PaperStructuresV
open Filter
open Asymptotics
open scoped BigOperators
open scoped Topology
export PalomarCorpus.E243_03.Shared (canonicalDenominator canonicalNaturalNumerator clearedIntegerNumerator prefixProduct)
/-- **The standing hypotheses of §`long243:sec:records`.** These are exactly the hypotheses of Problem `long243:res:problem`: a strictly increasing sequence of positive integers with `a (n+1) / a n ^ 2 → 1` and rational reciprocal sum, presented by an explicit integer numerator `num` and positive natural denominator `den`. The section's integer tails are the canonical ones constructed from this data; they are definitions below, not further hypotheses. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit, restated so the compared statements elaborate against Mathlib alone. -/
structure StandingOrbit where
  a : ℕ → ℕ
  num : ℤ
  den : ℕ
  a_strictMono : StrictMono a
  a_pos : ∀ n, 0 < a n
  den_pos : 0 < den
  hasSum : HasSum (fun n ↦ 1 / (a n : ℝ)) ((num : ℝ) / (den : ℝ))
  growth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)
/-- Local definition C, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.C (O : StandingOrbit) : ℕ → ℕ := canonicalNaturalNumerator O.a O.num O.den
/-- Local definition D, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.D (O : StandingOrbit) : ℕ → ℕ := canonicalDenominator O.a O.den
/-- Local definition EventuallySylvester, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.EventuallySylvester (O : StandingOrbit) : Prop :=
  ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1
/-- Local definition G, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.G (O : StandingOrbit) (n : ℕ) : ℕ := Nat.gcd (O.C n) (O.D n)
/-- Local definition u, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.u (O : StandingOrbit) (n : ℕ) : ℕ := O.C n / O.G n
/-- The running maximum `max_{k ≤ n} u k` of a natural-valued sequence, given by `runningMax u 0 = u 0` and `runningMax u (n+1) = max (runningMax u n) (u (n+1))`. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- Local definition R, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.R (O : StandingOrbit) : ℕ → ℕ := runningMax O.u
/-- Local definition v, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.v (O : StandingOrbit) (n : ℕ) : ℕ := O.D n / O.G n
/-- Local definition redErr, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.redErr (O : StandingOrbit) (n : ℕ) : ℤ := (O.v n : ℤ) - ((O.a n : ℤ) - 1) * (O.u n : ℤ)
/-- Local definition negPart, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.negPart (O : StandingOrbit) (n : ℕ) : ℕ := (-O.redErr n).toNat
/-- Local definition amp, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.amp (O : StandingOrbit) (n : ℕ) : ℝ := (O.R n : ℝ) * (O.negPart n : ℝ) / (O.u n : ℝ)
/-- Local definition canc, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.canc (O : StandingOrbit) (n : ℕ) : ℕ := O.G (n + 1) / O.G n
end PalomarCorpus.E243.PaperStructuresV
