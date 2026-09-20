/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.PaperCompleteR11.DensityTransport
import ErdosProblems.Erdos243.PaperCompleteR11.CanonicalRecords
import ErdosProblems.Erdos243.PaperCompleteR11.ArithmeticWeightedRecord
import ErdosProblems.Erdos243.PaperCompleteR11.QuantitativeRecordDichotomy
import ErdosProblems.Erdos243.PaperCompleteR11.InclusiveLimsup
import Solutions.PalomarCorpus.E243.Statement

open Filter Topology
open scoped BigOperators

set_option autoImplicit false

noncomputable section
namespace PalomarCorpus.E243.CompletePaperRecords
export PalomarCorpus.E243.Shared (canonicalDenominator canonicalNaturalNumerator centeredState clearedIntegerNumerator prefixProduct runningMax sylvesterNext)

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

theorem fixed_offsets_periodic_lowerDensity (E : Set ℕ) (s L T r : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hr : r < s) (offset : Fin L → ℕ)
    (hhit : ∀ n : ℕ, T ≤ n → n % s = r →
      ∃ i : Fin L, n + offset i ∈ E) :
    LowerDensityAtLeast E (1 / ((L : ℝ) * (s : ℝ))) := by
  have hLcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeDigitLcm q a n = ErdosProblems.Erdos243.cumulativeDigitLcm q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeDigitLcm, ErdosProblems.Erdos243.cumulativeDigitLcm, ih]
  have hDebt (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeOverlapDebt q a n = ErdosProblems.Erdos243.cumulativeOverlapDebt q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeOverlapDebt, ErdosProblems.Erdos243.cumulativeOverlapDebt, ih, hLcm]
  have hRun (u : ℕ → ℕ) (n : ℕ) :
      runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [runningMax, ErdosProblems.Erdos243.runningMax, ih]
  have hNatural (a : ℕ → ℕ) (p : ℤ) (q : ℕ) :
      canonicalNaturalNumerator a p q =
        ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator a p q := by
    funext n
    rfl
  have hLift (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedNumerator q a C = ErdosProblems.Erdos243.lcmLiftedNumerator q a C := by
    funext n
    simp only [lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, hDebt]
  have hDigit (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedDigit q a C = ErdosProblems.Erdos243.lcmLiftedDigit q a C := by
    funext n
    simp only [lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, hLcm, hLift]
  have hCharge (U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ) (f : ℝ → ℝ) :
      paperRecordCharge U V B f =
        ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge U V B f := by
    funext n
    rfl
  have h := ErdosProblems.Erdos243.PaperCompleteR11.fixed_offsets_periodic_lowerDensity E s L T r hs hL hr offset hhit
  try dsimp only [exceptionFinset, ErdosProblems.Erdos243.PaperCompleteR9.exceptionFinset, exceptionCount, ErdosProblems.Erdos243.PaperCompleteR9.exceptionCount, LowerDensityAtLeast, ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast, prefixProduct, ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, clearedIntegerNumerator, ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, canonicalNaturalNumerator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, canonicalDenominator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, IsStrictRecord, ErdosProblems.Erdos243.PaperCompleteR9.IsStrictRecord, IntegralUnbounded, ErdosProblems.Erdos243.PaperCompleteR11.IntegralUnbounded, canonicalLcmNumerator, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmNumerator, canonicalLcmDigit, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmDigit, paperRecordCharge, ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge, recordLogLog, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, negativeErrorLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.negativeErrorLogLogCharge, sylvesterNext, ErdosProblems.Erdos243.sylvesterNext, centeredState, ErdosProblems.Erdos243.centeredState] at h ⊢
  simpa only [hCharge, hNatural, hLift, hDigit, hLcm, hDebt, hRun] using h

theorem canonical_weighted_record_excess
    (a : ℕ → ℕ) (ha : StrictMono a) (hapos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (𝓝 1))
    (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : IntegralUnbounded f) :
    (∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = (a n : ℤ) ^ 2 - (a n : ℤ) + 1) ↔
      ∃ B : ℕ, Summable (paperRecordCharge (canonicalLcmNumerator a p q)
        (canonicalLcmDigit a p q) B f) := by
  have hLcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeDigitLcm q a n = ErdosProblems.Erdos243.cumulativeDigitLcm q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeDigitLcm, ErdosProblems.Erdos243.cumulativeDigitLcm, ih]
  have hDebt (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeOverlapDebt q a n = ErdosProblems.Erdos243.cumulativeOverlapDebt q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeOverlapDebt, ErdosProblems.Erdos243.cumulativeOverlapDebt, ih, hLcm]
  have hRun (u : ℕ → ℕ) (n : ℕ) :
      runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [runningMax, ErdosProblems.Erdos243.runningMax, ih]
  have hNatural (a : ℕ → ℕ) (p : ℤ) (q : ℕ) :
      canonicalNaturalNumerator a p q =
        ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator a p q := by
    funext n
    rfl
  have hLift (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedNumerator q a C = ErdosProblems.Erdos243.lcmLiftedNumerator q a C := by
    funext n
    simp only [lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, hDebt]
  have hDigit (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedDigit q a C = ErdosProblems.Erdos243.lcmLiftedDigit q a C := by
    funext n
    simp only [lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, hLcm, hLift]
  have hCharge (U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ) (f : ℝ → ℝ) :
      paperRecordCharge U V B f =
        ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge U V B f := by
    funext n
    rfl
  have h := ErdosProblems.Erdos243.PaperCompleteR11.canonical_weighted_record_excess a ha hapos p q hq hs hgrowth f hf hpos hdiv
  try dsimp only [exceptionFinset, ErdosProblems.Erdos243.PaperCompleteR9.exceptionFinset, exceptionCount, ErdosProblems.Erdos243.PaperCompleteR9.exceptionCount, LowerDensityAtLeast, ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast, prefixProduct, ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, clearedIntegerNumerator, ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, canonicalNaturalNumerator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, canonicalDenominator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, IsStrictRecord, ErdosProblems.Erdos243.PaperCompleteR9.IsStrictRecord, IntegralUnbounded, ErdosProblems.Erdos243.PaperCompleteR11.IntegralUnbounded, canonicalLcmNumerator, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmNumerator, canonicalLcmDigit, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmDigit, paperRecordCharge, ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge, recordLogLog, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, negativeErrorLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.negativeErrorLogLogCharge, sylvesterNext, ErdosProblems.Erdos243.sylvesterNext, centeredState, ErdosProblems.Erdos243.centeredState] at h ⊢
  simpa only [hCharge, hNatural, hLift, hDigit, hLcm, hDebt, hRun] using h

theorem arithmetic_weighted_record_dichotomy
    (a L U : ℕ → ℕ) (V : ℕ → ℤ)
    (ha : ∀ n, 0 < a n) (hLpos : ∀ n, 0 < L n) (hU : ∀ n, 0 < U n)
    (hL : ∀ n, L (n + 1) = Nat.lcm (L n) (a n))
    (hstate : ∀ n, (Nat.gcd (L n) (a n) : ℤ) * U (n + 1) =
      (U n : ℤ) - V n)
    (herror : ∀ n, V n = (L n : ℤ) - ((a n : ℤ) - 1) * U n)
    (hcenter : ∀ n, -(U n : ℤ) ≤ 2 * V n)
    (B : ℕ) (f : ℝ → ℝ) (hf : AntitoneOn f (Set.Ici 1))
    (hpos : ∀ x : ℝ, 1 ≤ x → 0 ≤ f x) (hdiv : IntegralUnbounded f) :
    (∃ H : ℕ, ∀ n, U n ≤ H) ↔ Summable (paperRecordCharge U V B f) := by
  have hLcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeDigitLcm q a n = ErdosProblems.Erdos243.cumulativeDigitLcm q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeDigitLcm, ErdosProblems.Erdos243.cumulativeDigitLcm, ih]
  have hDebt (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeOverlapDebt q a n = ErdosProblems.Erdos243.cumulativeOverlapDebt q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeOverlapDebt, ErdosProblems.Erdos243.cumulativeOverlapDebt, ih, hLcm]
  have hRun (u : ℕ → ℕ) (n : ℕ) :
      runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [runningMax, ErdosProblems.Erdos243.runningMax, ih]
  have hNatural (a : ℕ → ℕ) (p : ℤ) (q : ℕ) :
      canonicalNaturalNumerator a p q =
        ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator a p q := by
    funext n
    rfl
  have hLift (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedNumerator q a C = ErdosProblems.Erdos243.lcmLiftedNumerator q a C := by
    funext n
    simp only [lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, hDebt]
  have hDigit (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedDigit q a C = ErdosProblems.Erdos243.lcmLiftedDigit q a C := by
    funext n
    simp only [lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, hLcm, hLift]
  have hCharge (U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ) (f : ℝ → ℝ) :
      paperRecordCharge U V B f =
        ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge U V B f := by
    funext n
    rfl
  have h := ErdosProblems.Erdos243.PaperCompleteR11.arithmetic_weighted_record_dichotomy a L U V ha hLpos hU hL hstate herror hcenter B f hf hpos hdiv
  try dsimp only [exceptionFinset, ErdosProblems.Erdos243.PaperCompleteR9.exceptionFinset, exceptionCount, ErdosProblems.Erdos243.PaperCompleteR9.exceptionCount, LowerDensityAtLeast, ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast, prefixProduct, ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, clearedIntegerNumerator, ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, canonicalNaturalNumerator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, canonicalDenominator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, IsStrictRecord, ErdosProblems.Erdos243.PaperCompleteR9.IsStrictRecord, IntegralUnbounded, ErdosProblems.Erdos243.PaperCompleteR11.IntegralUnbounded, canonicalLcmNumerator, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmNumerator, canonicalLcmDigit, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmDigit, paperRecordCharge, ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge, recordLogLog, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, negativeErrorLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.negativeErrorLogLogCharge, sylvesterNext, ErdosProblems.Erdos243.sylvesterNext, centeredState, ErdosProblems.Erdos243.centeredState] at h ⊢
  simpa only [hCharge, hNatural, hLift, hDigit, hLcm, hDebt, hRun] using h

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
  have hLcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeDigitLcm q a n = ErdosProblems.Erdos243.cumulativeDigitLcm q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeDigitLcm, ErdosProblems.Erdos243.cumulativeDigitLcm, ih]
  have hDebt (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeOverlapDebt q a n = ErdosProblems.Erdos243.cumulativeOverlapDebt q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeOverlapDebt, ErdosProblems.Erdos243.cumulativeOverlapDebt, ih, hLcm]
  have hRun (u : ℕ → ℕ) (n : ℕ) :
      runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [runningMax, ErdosProblems.Erdos243.runningMax, ih]
  have hNatural (a : ℕ → ℕ) (p : ℤ) (q : ℕ) :
      canonicalNaturalNumerator a p q =
        ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator a p q := by
    funext n
    rfl
  have hLift (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedNumerator q a C = ErdosProblems.Erdos243.lcmLiftedNumerator q a C := by
    funext n
    simp only [lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, hDebt]
  have hDigit (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedDigit q a C = ErdosProblems.Erdos243.lcmLiftedDigit q a C := by
    funext n
    simp only [lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, hLcm, hLift]
  have hCharge (U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ) (f : ℝ → ℝ) :
      paperRecordCharge U V B f =
        ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge U V B f := by
    funext n
    rfl
  have h := ErdosProblems.Erdos243.PaperCompleteR11.canonical_quantitative_record_dichotomy a ha hapos p q hq hs hgrowth hnot
  try dsimp only [exceptionFinset, ErdosProblems.Erdos243.PaperCompleteR9.exceptionFinset, exceptionCount, ErdosProblems.Erdos243.PaperCompleteR9.exceptionCount, LowerDensityAtLeast, ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast, prefixProduct, ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, clearedIntegerNumerator, ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, canonicalNaturalNumerator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, canonicalDenominator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, IsStrictRecord, ErdosProblems.Erdos243.PaperCompleteR9.IsStrictRecord, IntegralUnbounded, ErdosProblems.Erdos243.PaperCompleteR11.IntegralUnbounded, canonicalLcmNumerator, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmNumerator, canonicalLcmDigit, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmDigit, paperRecordCharge, ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge, recordLogLog, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, negativeErrorLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.negativeErrorLogLogCharge, sylvesterNext, ErdosProblems.Erdos243.sylvesterNext, centeredState, ErdosProblems.Erdos243.centeredState] at h ⊢
  simpa only [hCharge, hNatural, hLift, hDigit, hLcm, hDebt, hRun] using h

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
  have hLcm (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeDigitLcm q a n = ErdosProblems.Erdos243.cumulativeDigitLcm q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeDigitLcm, ErdosProblems.Erdos243.cumulativeDigitLcm, ih]
  have hDebt (q : ℕ) (a : ℕ → ℕ) (n : ℕ) :
      cumulativeOverlapDebt q a n = ErdosProblems.Erdos243.cumulativeOverlapDebt q a n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [cumulativeOverlapDebt, ErdosProblems.Erdos243.cumulativeOverlapDebt, ih, hLcm]
  have hRun (u : ℕ → ℕ) (n : ℕ) :
      runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
    induction n with
    | zero => rfl
    | succ n ih => simpa only [runningMax, ErdosProblems.Erdos243.runningMax, ih]
  have hNatural (a : ℕ → ℕ) (p : ℤ) (q : ℕ) :
      canonicalNaturalNumerator a p q =
        ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator a p q := by
    funext n
    rfl
  have hLift (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedNumerator q a C = ErdosProblems.Erdos243.lcmLiftedNumerator q a C := by
    funext n
    simp only [lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, hDebt]
  have hDigit (q : ℕ) (a C : ℕ → ℕ) :
      lcmLiftedDigit q a C = ErdosProblems.Erdos243.lcmLiftedDigit q a C := by
    funext n
    simp only [lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, hLcm, hLift]
  have hCharge (U : ℕ → ℕ) (V : ℕ → ℤ) (B : ℕ) (f : ℝ → ℝ) :
      paperRecordCharge U V B f =
        ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge U V B f := by
    funext n
    rfl
  have h := ErdosProblems.Erdos243.PaperCompleteR11.canonical_inclusive_logLog_criterion a ha hapos p q hq hs hgrowth hlim
  try dsimp only [exceptionFinset, ErdosProblems.Erdos243.PaperCompleteR9.exceptionFinset, exceptionCount, ErdosProblems.Erdos243.PaperCompleteR9.exceptionCount, LowerDensityAtLeast, ErdosProblems.Erdos243.PaperCompleteR11.LowerDensityAtLeast, prefixProduct, ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, clearedIntegerNumerator, ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, canonicalNaturalNumerator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, canonicalDenominator, ErdosProblems.Erdos243.PaperCompleteR7.canonicalDenominator, lcmLiftedNumerator, ErdosProblems.Erdos243.lcmLiftedNumerator, lcmLiftedDigit, ErdosProblems.Erdos243.lcmLiftedDigit, IsStrictRecord, ErdosProblems.Erdos243.PaperCompleteR9.IsStrictRecord, IntegralUnbounded, ErdosProblems.Erdos243.PaperCompleteR11.IntegralUnbounded, canonicalLcmNumerator, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmNumerator, canonicalLcmDigit, ErdosProblems.Erdos243.PaperCompleteR11.canonicalLcmDigit, paperRecordCharge, ErdosProblems.Erdos243.PaperCompleteR11.paperRecordCharge, recordLogLog, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, recordLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, recordTheta, ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, negativeErrorLogLogCharge, ErdosProblems.Erdos243.PaperCompleteR11.negativeErrorLogLogCharge, sylvesterNext, ErdosProblems.Erdos243.sylvesterNext, centeredState, ErdosProblems.Erdos243.centeredState] at h ⊢
  simpa only [hCharge, hNatural, hLift, hDigit, hLcm, hDebt, hRun] using h

end PalomarCorpus.E243.CompletePaperRecords
end
