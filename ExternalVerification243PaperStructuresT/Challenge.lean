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
`ErdosProblems.Erdos243.PaperCompleteR21.AmplifiedRecordEquivalence`,
`ErdosProblems.Erdos243.PaperCompleteR21.ReducedDenominatorPrimePowers`,
`ErdosProblems.Erdos243.PaperCompleteR7.CanonicalState`,
`ErdosProblems.Erdos243.PrimitiveRecordBarrier`.
-/

open Filter
open Asymptotics
open scoped BigOperators
open scoped Topology

namespace Erdos249257.ExternalVerification243PaperStructuresT

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

noncomputable def StandingOrbit.EventuallySylvester (O : StandingOrbit) : Prop :=
  ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1

noncomputable def StandingOrbit.G (O : StandingOrbit) (n : ℕ) : ℕ := Nat.gcd (O.C n) (O.D n)

noncomputable def StandingOrbit.u (O : StandingOrbit) (n : ℕ) : ℕ := O.C n / O.G n

noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

noncomputable def StandingOrbit.R (O : StandingOrbit) : ℕ → ℕ := runningMax O.u

noncomputable def StandingOrbit.v (O : StandingOrbit) (n : ℕ) : ℕ := O.D n / O.G n

noncomputable def StandingOrbit.redErr (O : StandingOrbit) (n : ℕ) : ℤ := (O.v n : ℤ) - ((O.a n : ℤ) - 1) * (O.u n : ℤ)

noncomputable def StandingOrbit.negPart (O : StandingOrbit) (n : ℕ) : ℕ := (-O.redErr n).toNat

noncomputable def StandingOrbit.amp (O : StandingOrbit) (n : ℕ) : ℝ := (O.R n : ℝ) * (O.negPart n : ℝ) / (O.u n : ℝ)

noncomputable def StandingOrbit.canc (O : StandingOrbit) (n : ℕ) : ℕ := O.G (n + 1) / O.G n

noncomputable def StandingOrbit.delta (O : StandingOrbit) (n : ℕ) : ℝ :=
  max 0 ((O.a n : ℝ) ^ 2 / (O.a (n + 1) : ℝ) - 1)

/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R_delta_sub_amp_tendsto_zero in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem R_delta_sub_amp_tendsto_zero (O : StandingOrbit) :
    Tendsto (fun n ↦ (O.R n : ℝ) * O.delta n - O.amp n) atTop (𝓝 0) := by
  sorry

/-- States long243:res:criticalrate from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R_le_of_u_le in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem R_le_of_u_le (O : StandingOrbit) {c N : ℕ} (h : ∀ n, N ≤ n → O.u n ≤ c * n) :
    ∀ n, N ≤ n → O.R n ≤ O.R N + c * n := by
  sorry

/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Rdelta_bddAbove_iff_amp in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem Rdelta_bddAbove_iff_amp (O : StandingOrbit) :
    (∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K) ↔
      (∃ K : ℝ, ∀ᶠ n in atTop, (O.R n : ℝ) * O.delta n ≤ K) := by
  sorry

/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp_bddAbove_iff_sylvester in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem amp_bddAbove_iff_sylvester (O : StandingOrbit) :
    O.EventuallySylvester ↔ ∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K := by
  sorry

/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.coprimeMultiplier_cofinal in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeMultiplier_cofinal (O : StandingOrbit) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) := by
  sorry

/-- States long243:res:criticalrate from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem criticalRate (O : StandingOrbit)
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ))) :
    (O.EventuallySylvester ↔ (fun n : ℕ ↦ (O.u n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ))) ∧
      (O.EventuallySylvester ↔
        (fun n : ℕ ↦ (O.negPart n : ℝ)) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ))) := by
  sorry

/-- States long243:res:criticalrate from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate_counterexample in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem criticalRate_counterexample (O : StandingOrbit)
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)))
    (hns : ¬ O.EventuallySylvester) :
    Filter.limsup (fun n ↦ (((O.u n : ℝ) / (n : ℝ) : ℝ) : EReal)) atTop = ⊤ ∧
      Filter.limsup (fun n ↦ ((O.negPart n : ℝ) : EReal)) atTop = ⊤ := by
  sorry

/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta_negPart_comparison in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem delta_negPart_comparison (O : StandingOrbit) :
    ∃ N, ∀ n, N ≤ n →
      |O.delta n - (O.negPart n : ℝ) / (O.u n : ℝ)| ≤ 3 / (O.a n : ℝ) := by
  sorry

/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.largePrime_coprimeMultiplier in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem largePrime_coprimeMultiplier (O : StandingOrbit) (B : ℕ) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) ∧
      ∃ p, Nat.Prime p ∧ p ∣ O.a n ∧ B < p := by
  sorry

/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.primeBlock_supply in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem primeBlock_supply (O : StandingOrbit) (B N₀ : ℕ) (hcanc : ∀ m, N₀ ≤ m → O.canc m ≤ B) :
    ∀ j : ℕ, ∃ T, N₀ ≤ T ∧ ∃ P : Finset ℕ, P.card = j ∧
      ∀ p ∈ P, Nat.Prime p ∧ B < p ∧ p ∣ O.v T := by
  sorry

/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported
from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.recordAmplified in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem recordAmplified (O : StandingOrbit) :
    (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (O.EventuallySylvester ↔
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop ≠ ⊤) ∧
      (Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ ((O.amp n : ℝ) : EReal)) atTop = ⊤) ∧
      (Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = 0 ∨
        Filter.limsup (fun n ↦ (((O.R n : ℝ) * O.delta n : ℝ) : EReal)) atTop = ⊤) := by
  sorry

end Erdos249257.ExternalVerification243PaperStructuresT
