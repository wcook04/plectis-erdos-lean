/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for summable-negative-mass rigidity in Erdős #243

For the exact product-cleared reciprocal-tail orbit, division-free normalized
vanishing together with summability of the normalized negative centered mass
forces both eventual zero centered state and the exact Sylvester recurrence.

The theorem is conditional on its displayed hypotheses.  It does not prove
that every orbit associated with Erdős #243 satisfies the summability or
normalized-vanishing assumptions, and the unrestricted problem remains open.
-/

namespace Erdos249257.ExternalVerification243SummableNegativeMassRigidity

/-- The Sylvester successor map. -/
def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

/-- Product-cleared denominator update. -/
def nextDenState (a D : ℤ) : ℤ :=
  a * D

/-- Product-cleared reciprocal-tail update. -/
def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D

/-- Centered reciprocal-tail error. -/
def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C

/-- Normalized mass of the negative part of an integral tail step. -/
noncomputable def negativeRelativeMass
    (C : ℕ → ℕ) (E : ℕ → ℤ) (n : ℕ) : ℝ :=
  (Int.natAbs (min (E n) 0) : ℝ) / C n

/-- Complete rigidity of the summable normalized-negative-mass branch: the
centered defect vanishes eventually and the orbit consequently follows the
exact Sylvester recurrence eventually. -/
theorem summableNegativeMass_completeRigidity
    (a D : ℕ → ℤ) (C : ℕ → ℕ)
    (hD : ∀ n, D (n + 1) = nextDenState (a n) (D n))
    (hC : ∀ n, (C (n + 1) : ℤ) = nextTailState (a n) (D n) (C n))
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) =
      (C n : ℤ) - centeredState (a n) (D n) (C n))
    (hvanish : ∀ K, ∃ N, ∀ n, N ≤ n →
      K * Int.natAbs (centeredState (a n) (D n) (C n)) < C n)
    (hsum : Summable (negativeRelativeMass C
      (fun n ↦ centeredState (a n) (D n) (C n)))) :
    (∃ N, ∀ n, N ≤ n → centeredState (a n) (D n) (C n) = 0) ∧
      ∃ N, ∀ n, N ≤ n → a (n + 1) = sylvesterNext (a n) := by
  sorry


open scoped BigOperators
open Finset

def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j

def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)

def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat

def canonicalDenominator (a : ℕ → ℕ) (q n : ℕ) : ℕ :=
  q * prefixProduct a n


theorem finite_negative_mass_scalar (C : ℕ → ℕ) (E : ℕ → ℤ)
    (hCpos : ∀ n, 0 < C n)
    (hstep : ∀ n, (C (n + 1) : ℤ) = (C n : ℤ) - E n)
    (hsum : Summable (negativeRelativeMass C E)) :
    ∃ N, ∀ n, N ≤ n → E n = 0 := by
  sorry

theorem canonical_finite_negative_mass
    (a : ℕ → ℕ) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n => 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hmass : Summable (fun n =>
      max (-(centeredState (a n : ℤ) (canonicalDenominator a q n : ℤ)
        (canonicalNaturalNumerator a p q n : ℤ) : ℝ)) 0 /
          (canonicalNaturalNumerator a p q n : ℝ))) :
    ∃ N, ∀ n, N ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry

end Erdos249257.ExternalVerification243SummableNegativeMassRigidity
