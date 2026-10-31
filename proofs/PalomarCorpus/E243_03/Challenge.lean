/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, record sections 7.1 to 7.2: how fast the running maximum must increase; bounds that allow for cancellation and earlier decreases

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
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
/-- Outside eventual Sylvester recurrence, either numerator-denominator gcds are unbounded and recordTheta is infinite, or the gcd eventually equals a positive g and recordTheta satisfies the displayed totient-ratio bounds and strictly exceeds g. -/
theorem canonical_quantitative_record_dichotomy
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    ((∀ B : ℕ, ∃ n, B < Nat.gcd (C n) (D n)) ∧ recordTheta C = ⊤) ∨
    ∃ N g : ℕ, 0 < g ∧ (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
      (∀ T : ℕ, N + 2 ≤ T →
        (((g : ℝ) * (D T / g : ℕ) / Nat.totient (D T / g) : ℝ) : EReal) ≤ recordTheta C) ∧
      (g : EReal) < recordTheta C := by
  sorry
/-- Under the rational-sum and growth hypotheses, a limit superior of the normalized negative error at most one forces eventual Sylvester recurrence, including the boundary value one. -/
theorem canonical_inclusive_logLog_criterion
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hlim : let C := canonicalNaturalNumerator a p q
      let D := canonicalDenominator a q
      let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
      limsup (fun n ↦ (negativeErrorLogLogCharge C E n : EReal)) atTop ≤ 1) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
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
/-- States long243:res:recorddichotomy from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR11.canonical_recordTheta_eq_zero_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_recordTheta_eq_zero_iff
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)) :
    recordTheta (canonicalNaturalNumerator a p q) = 0 ↔
      ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry
/-- States long243:res:recorddichotomy from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR11.canonical_recordTheta_gt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_recordTheta_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    (1 : EReal) < recordTheta (canonicalNaturalNumerator a p q) := by
  sorry
/-- States long243:res:recorddichotomy from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR11.canonical_recordTheta_zero_or_gt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_recordTheta_zero_or_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1)) :
    recordTheta (canonicalNaturalNumerator a p q) = 0 ∨
      (1 : EReal) < recordTheta (canonicalNaturalNumerator a p q) := by
  sorry
end PalomarCorpus.E243.PaperStatementsM

namespace PalomarCorpus.E243.PaperStatementsI
open Filter
open scoped Topology
open scoped BigOperators
export PalomarCorpus.E243_03.Shared (canonicalDenominator canonicalNaturalNumerator centeredState clearedIntegerNumerator negativeErrorLogLogCharge prefixProduct recordLogLog sylvesterNext)
/-- States long243:res:loglogboundary from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR11.canonical_negativeError_limsup_gt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_negativeError_limsup_gt_one
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2) atTop (𝓝 1))
    (hnot : ¬ ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ)) :
    let C := canonicalNaturalNumerator a p q
    let D := canonicalDenominator a q
    let E := fun n ↦ centeredState (a n : ℤ) (D n : ℤ) (C n : ℤ)
    (1 : EReal) < limsup (fun n ↦ (negativeErrorLogLogCharge C E n : EReal)) atTop := by
  sorry
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
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.R_delta_sub_amp_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem R_delta_sub_amp_tendsto_zero (O : StandingOrbit) :
    Tendsto (fun n ↦ (O.R n : ℝ) * O.delta n - O.amp n) atTop (𝓝 0) := by
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
/-- States long243:res:recordamplified from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.StandingOrbit.canc_lt_of_amp_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canc_lt_of_amp_le (O : StandingOrbit) (hns : ¬ O.EventuallySylvester) (K : ℕ) (hK1 : 1 ≤ K)
    (N₀ : ℕ) (hbd : ∀ n, N₀ ≤ n → O.amp n ≤ (K : ℝ)) :
    ∃ N, ∀ s, N ≤ s → O.canc s < 2 * K := by
  sorry
end PalomarCorpus.E243.PaperStructuresV
