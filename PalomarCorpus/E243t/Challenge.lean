/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band t

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Asymptotics
open scoped BigOperators
open scoped Topology

namespace PalomarCorpus.E243.PaperStructuresT
open Filter
open Asymptotics
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
/-- Local definition EventuallySylvester, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.EventuallySylvester (O : StandingOrbit) : Prop :=
  ∃ N, ∀ n, N ≤ n → (O.a (n + 1) : ℤ) = (O.a n : ℤ) ^ 2 - (O.a n : ℤ) + 1
/-- Local definition G, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.G (O : StandingOrbit) (n : ℕ) : ℕ := Nat.gcd (O.C n) (O.D n)
/-- Local definition u, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def StandingOrbit.u (O : StandingOrbit) (n : ℕ) : ℕ := O.C n / O.G n
/-- Running maximum `R n = max_{k ≤ n} u k` of a numerator sequence. Local copy of ErdosProblems.Erdos243.runningMax, restated so the compared statements elaborate against Mathlib alone. -/
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
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R_delta_sub_amp_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem R_delta_sub_amp_tendsto_zero (O : StandingOrbit) :
    Tendsto (fun n ↦ (O.R n : ℝ) * O.delta n - O.amp n) atTop (𝓝 0) := by
  sorry
/-- States long243:res:criticalrate from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R_le_of_u_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem R_le_of_u_le (O : StandingOrbit) {c N : ℕ} (h : ∀ n, N ≤ n → O.u n ≤ c * n) :
    ∀ n, N ≤ n → O.R n ≤ O.R N + c * n := by
  sorry
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.Rdelta_bddAbove_iff_amp in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem Rdelta_bddAbove_iff_amp (O : StandingOrbit) :
    (∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K) ↔
      (∃ K : ℝ, ∀ᶠ n in atTop, (O.R n : ℝ) * O.delta n ≤ K) := by
  sorry
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.amp_bddAbove_iff_sylvester in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem amp_bddAbove_iff_sylvester (O : StandingOrbit) :
    O.EventuallySylvester ↔ ∃ K : ℝ, ∀ᶠ n in atTop, O.amp n ≤ K := by
  sorry
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.coprimeMultiplier_cofinal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem coprimeMultiplier_cofinal (O : StandingOrbit) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) := by
  sorry
/-- States long243:res:criticalrate from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem criticalRate (O : StandingOrbit)
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ))) :
    (O.EventuallySylvester ↔ (fun n : ℕ ↦ (O.u n : ℝ)) =O[atTop] (fun n : ℕ ↦ (n : ℝ))) ∧
      (O.EventuallySylvester ↔
        (fun n : ℕ ↦ (O.negPart n : ℝ)) =O[atTop] (fun _ : ℕ ↦ (1 : ℝ))) := by
  sorry
/-- States long243:res:criticalrate from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.criticalRate_counterexample in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem criticalRate_counterexample (O : StandingOrbit)
    (hδ : (fun n : ℕ ↦ O.delta n) =O[atTop] (fun n : ℕ ↦ 1 / (n : ℝ)))
    (hns : ¬ O.EventuallySylvester) :
    Filter.limsup (fun n ↦ (((O.u n : ℝ) / (n : ℝ) : ℝ) : EReal)) atTop = ⊤ ∧
      Filter.limsup (fun n ↦ ((O.negPart n : ℝ) : EReal)) atTop = ⊤ := by
  sorry
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.delta_negPart_comparison in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem delta_negPart_comparison (O : StandingOrbit) :
    ∃ N, ∀ n, N ≤ n →
      |O.delta n - (O.negPart n : ℝ) / (O.u n : ℝ)| ≤ 3 / (O.a n : ℝ) := by
  sorry
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.largePrime_coprimeMultiplier in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem largePrime_coprimeMultiplier (O : StandingOrbit) (B : ℕ) (N : ℕ) :
    ∃ n, N ≤ n ∧ Nat.Coprime (O.a n) (O.D n) ∧
      ∃ p, Nat.Prime p ∧ p ∣ O.a n ∧ B < p := by
  sorry
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.primeBlock_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem primeBlock_supply (O : StandingOrbit) (B N₀ : ℕ) (hcanc : ∀ m, N₀ ≤ m → O.canc m ≤ B) :
    ∀ j : ℕ, ∃ T, N₀ ≤ T ∧ ∃ P : Finset ℕ, P.card = j ∧
      ∀ p ∈ P, Nat.Prime p ∧ B < p ∧ p ∣ O.v T := by
  sorry
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.recordAmplified in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
end PalomarCorpus.E243.PaperStructuresT
