/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band u

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
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
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energySqrt_summable_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energySqrt_summable_iff (O : StandingOrbit) :
    Summable O.energySqrt ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  sorry
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_criterion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energy_criterion (O : StandingOrbit) :
    (Summable O.energy ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ∧
      (Summable O.energySqrt ↔
        ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) := by
  sorry
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_le_two_energySqrt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energy_le_two_energySqrt (O : StandingOrbit) (n : ℕ) : O.energy n ≤ 2 * O.energySqrt n := by
  sorry
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.energy_summable_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem energy_summable_iff (O : StandingOrbit) :
    Summable O.energy ↔
      ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1 := by
  sorry
/-- States long243:res:energycriterion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.exists_late_energy_window in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_late_energy_window (O : StandingOrbit) (hunb : ∀ M : ℕ, ∃ n, M < O.u n) (S : ℕ) :
    ∃ (s τ : ℕ) (J : Finset ℕ), S ≤ s ∧ s < τ ∧ (∀ n ∈ J, s ≤ n ∧ n < τ) ∧
      (1 : ℝ) / 16 ≤ ∑ n ∈ J, O.energy n := by
  sorry
/-- States long243:res:oddpowersupply from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.oddPrimePower_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem oddPrimePower_supply (O : StandingOrbit) (A : ℝ) (hA : 0 < A) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧ Odd (p ^ k) ∧
      p ^ k ∣ O.v n ∧ ((O.Hmax n : ℝ) + 2) ^ A < ((p ^ k : ℕ) : ℝ) := by
  sorry
/-- States long243:res:oddpowersupply from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.oddPrimePower_supply_nat in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem oddPrimePower_supply_nat (O : StandingOrbit) (A : ℕ) :
    ∃ N, ∀ n, N ≤ n → ∃ p k : ℕ, p.Prime ∧ p ≠ 2 ∧ 1 ≤ k ∧
      p ^ k ∣ O.v n ∧ (O.Hmax n + 2) ^ A < p ^ k := by
  sorry
/-- States long243:res:unitrecord from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.unitRecordIncrement_criterion in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem unitRecordIncrement_criterion (O : StandingOrbit) :
    (∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1) ↔
      {n : ℕ | 2 ≤ O.R (n + 1) - O.R n}.Finite := by
  sorry
end PalomarCorpus.E243.PaperStructuresU
