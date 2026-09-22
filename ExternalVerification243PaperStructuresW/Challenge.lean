/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #243

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos243.PaperCompleteR21.ReducedDenominatorPrimePowers`,
`ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState`,
`ErdosProblems.Erdos243.PrimitiveRecordBarrier`.
-/

open Filter
open scoped BigOperators
open scoped Topology

namespace Erdos249257.ExternalVerification243PaperStructuresW

structure StandingOrbit where
  /-- The multiplier sequence `a n`. -/
  a : ℕ → ℕ
  /-- The numerator of the rational reciprocal sum. -/
  num : ℤ
  /-- The denominator of the rational reciprocal sum. -/
  den : ℕ
  /-- `1 ≤ a 1 < a 2 < ⋯`. -/
  a_strictMono : StrictMono a
  /-- Positivity of the multipliers. -/
  a_pos : ∀ n, 0 < a n
  /-- Positivity of the denominator of the sum. -/
  den_pos : 0 < den
  /-- `∑ 1 / a n = num / den ∈ ℚ`. -/
  hasSum : HasSum (fun n ↦ 1 / (a n : ℝ)) ((num : ℝ) / (den : ℝ))
  /-- `a (n+1) / a n ^ 2 → 1`. -/
  growth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)

noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

noncomputable def StandingOrbit.C (O : StandingOrbit) : ℕ → ℕ := canonicalNaturalNumerator O.a O.num O.den

noncomputable def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n

noncomputable def StandingOrbit.D (O : StandingOrbit) : ℕ → ℕ := canonicalDenominator O.a O.den

noncomputable def StandingOrbit.G (O : StandingOrbit) (n : ℕ) : ℕ := Nat.gcd (O.C n) (O.D n)

noncomputable def StandingOrbit.u (O : StandingOrbit) (n : ℕ) : ℕ := O.C n / O.G n

noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

noncomputable def StandingOrbit.R (O : StandingOrbit) : ℕ → ℕ := runningMax O.u

/-- States long243:res:unitrecord from the long record for Erdős problem #243. Transported from
ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.unitRecordIncrement_sylvesterNext in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem unitRecordIncrement_sylvesterNext (O : StandingOrbit)
    (hinc : ∃ N, ∀ n, N ≤ n → O.R (n + 1) - O.R n ≤ 1) :
    ∃ M, ∀ n, M ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  sorry

end Erdos249257.ExternalVerification243PaperStructuresW
