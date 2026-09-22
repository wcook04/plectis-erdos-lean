/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243u

Every non-theorem declaration of `PalomarCorpus/E243u/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E243.PaperStructuresU
open Filter
open scoped BigOperators
open scoped Topology
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
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
/-- Local definition C, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.C (O : StandingOrbit) : ℕ → ℕ := canonicalNaturalNumerator O.a O.num O.den
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n
/-- Local definition D, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.D (O : StandingOrbit) : ℕ → ℕ := canonicalDenominator O.a O.den
/-- Local definition G, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.G (O : StandingOrbit) (n : ℕ) : ℕ := Nat.gcd (O.C n) (O.D n)
/-- Local definition u, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.u (O : StandingOrbit) (n : ℕ) : ℕ := O.C n / O.G n
/-- Running maximum `R n = max_{k ≤ n} u k` of a numerator sequence. Local copy of ErdosProblems.Erdos243.runningMax, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- Local definition Hmax, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.Hmax (O : StandingOrbit) : ℕ → ℕ := runningMax O.C
/-- Local definition R, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.R (O : StandingOrbit) : ℕ → ℕ := runningMax O.u
/-- Local definition jump, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.jump (O : StandingOrbit) (n : ℕ) : ℕ := O.u (n + 1) - O.u n
/-- Local definition energy, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.energy (O : StandingOrbit) (n : ℕ) : ℝ :=
  if O.R n < O.u (n + 1) then
    (if 3 ≤ O.jump n then 1 / Real.sqrt ((O.u n : ℝ)) else 0)
      + ((O.jump n - 2 : ℕ) : ℝ) / (O.u n : ℝ)
  else 0
/-- Local definition energySqrt, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.energySqrt (O : StandingOrbit) (n : ℕ) : ℝ :=
  if O.R n < O.u (n + 1) then ((O.jump n - 2 : ℕ) : ℝ) / Real.sqrt ((O.u n : ℝ))
  else 0
/-- Local definition v, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.v (O : StandingOrbit) (n : ℕ) : ℕ := O.D n / O.G n
end PalomarCorpus.E243.PaperStructuresU
