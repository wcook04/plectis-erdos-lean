/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

set_option autoImplicit false

noncomputable section
namespace Erdos249257.ExternalVerification243CompletePaperRecords
open Filter Topology
open scoped BigOperators

noncomputable local instance (p : Prop) : Decidable p := Classical.propDecidable p

noncomputable def exceptionFinset (E : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n ↦ n ∈ E)

noncomputable def exceptionCount (E : Set ℕ) (X : ℕ) : ℕ :=
  (exceptionFinset E X).card

def LowerDensityAtLeast (E : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    (d - ε) * (X : ℝ) ≤ (exceptionCount E X : ℝ)

def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n

def cumulativeDigitLcm (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => q
  | n + 1 => Nat.lcm (cumulativeDigitLcm q a n) (a n)

def cumulativeOverlapDebt (q : ℕ) (a : ℕ → ℕ) : ℕ → ℕ
  | 0 => 1
  | n + 1 =>
      cumulativeOverlapDebt q a n *
        Nat.gcd (cumulativeDigitLcm q a n) (a n)

def lcmLiftedNumerator (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℕ :=
  C n / cumulativeOverlapDebt q a n

def lcmLiftedDigit (q : ℕ) (a C : ℕ → ℕ) (n : ℕ) : ℤ :=
  (cumulativeDigitLcm q a n : ℤ) -
    ((a n : ℤ) - 1) * (lcmLiftedNumerator q a C n : ℤ)

def IsStrictRecord (U : ℕ → ℕ) (n : ℕ) : Prop :=
  ∀ j, j ≤ n → U j < U (n + 1)

def IntegralUnbounded (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ R : ℝ, 1 ≤ R ∧ M < ∫ t in (1 : ℝ)..R, f t

noncomputable def canonicalLcmNumerator (a : ℕ → ℕ) (p : ℤ) (q : ℕ) : ℕ → ℕ :=
  lcmLiftedNumerator q a (canonicalNaturalNumerator a p q)

noncomputable def canonicalLcmDigit (a : ℕ → ℕ) (p : ℤ) (q : ℕ) : ℕ → ℤ :=
  lcmLiftedDigit q a (canonicalNaturalNumerator a p q)

noncomputable def paperRecordCharge (U : ℕ → ℕ) (V : ℕ → ℤ)
    (B : ℕ) (f : ℝ → ℝ) (n : ℕ) : ℝ := by
  classical
  exact if IsStrictRecord U n then
    ((max (-V n - (B : ℤ)) 0 : ℤ) : ℝ) * f (U n : ℝ)
  else 0

def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2

noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)

noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop

noncomputable def negativeErrorLogLogCharge (U : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  ((max (-E n) 0 : ℤ) : ℝ) / recordLogLog (U n)

def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

theorem fixed_offsets_periodic_lowerDensity (E : Set ℕ) (s L T r : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hr : r < s) (offset : Fin L → ℕ)
    (hhit : ∀ n : ℕ, T ≤ n → n % s = r →
      ∃ i : Fin L, n + offset i ∈ E) :
    LowerDensityAtLeast E (1 / ((L : ℝ) * (s : ℝ))) := by
  sorry

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
  sorry

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
  sorry

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

end Erdos249257.ExternalVerification243CompletePaperRecords
end
