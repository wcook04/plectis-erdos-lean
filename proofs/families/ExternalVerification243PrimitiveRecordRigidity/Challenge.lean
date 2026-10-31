/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for primitive record-rise-two rigidity in Erdős #243

The compared chain is the finite arithmetic of a dynamically reduced
reciprocal tail with arbitrary cancellation: a prime power in the reduced
denominator cannot drop while the raw numerator stays below the next power;
it persists up to a first height crossing; an odd multiple of that prime
above the running numerator maximum is unreachable under record jumps of
size at most two; a large odd prime power supplies such a trap height; a
vanishing centred error forces a unit numerator; two consecutive zeros pin
the Sylvester step; and, given a late fresh odd prime-power supply, the
multipliers eventually follow `a ↦ a² - a + 1`.

The composed consumer is conditional on its explicit hypotheses, in
particular the record-jump bound and the fresh odd prime-power supply.
Neither is derived from the unrestricted dynamics here. The Challenge
imports only Mathlib. It does not settle Erdős #243.
-/

namespace Erdos249257.ExternalVerification243PrimitiveRecordRigidity

/-- The Sylvester successor map. -/
def sylvesterNext (a : ℤ) : ℤ :=
  a ^ 2 - a + 1

/-- Running maximum `R n = max_{k ≤ n} u k` of a numerator sequence. -/
def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

/-- **Valuation-loss threshold.** For one primitive step with arbitrary
cancellation `hc`, a prime power dividing the reduced denominator survives
the step as long as the raw numerator stays below the next power of `p`. -/
theorem primitive_valuation_no_drop
    {a u v w hc u' v' p l : ℕ}
    (hp : p.Prime)
    (hcop : Nat.Coprime u v)
    (hvpos : 0 < v)
    (hq : w + v = a * u)
    (hwpos : 0 < w)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (hl : p ^ l ∣ v)
    (hlt : w < p ^ (l + 1)) :
    p ^ l ∣ v' := by
  sorry

/-- **Protected prime power.** Along a primitive orbit with arbitrary
cancellation satisfying the centring bound `2 * w n ≤ 3 * u n` from index
`s`, a prime power `p ^ l ∣ v s` divides `v n` at every later index whose
strictly earlier window stays below height `H`, provided
`3 * H < 2 * p ^ (l + 1)`. -/
theorem protectedPrimePower_persists
    (a u v w hc : ℕ → ℕ) (p l s H : ℕ)
    (hp : p.Prime)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hheight : 3 * H < 2 * p ^ (l + 1))
    (hprot : p ^ l ∣ v s) :
    ∀ n, s ≤ n → (∀ k, s ≤ k → k < n → u k < H) → p ^ l ∣ v n := by
  sorry

/-- **Odd protected cut.** If the primitive orbit satisfies the centring
bound from index `s`, `p ^ l ∣ v s` for an odd height `H` that is a
multiple of `p` with `runningMax u s < H` and `3 * H < 2 * p ^ (l + 1)`,
and every record-setting step from `s` onward rises by at most `2`, then
the orbit never reaches `H`. -/
theorem odd_record_cut
    (a u v w hc : ℕ → ℕ) (p l s H : ℕ)
    (hp : p.Prime)
    (hl : 1 ≤ l)
    (hHodd : Odd H)
    (hpH : p ∣ H)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hheight : 3 * H < 2 * p ^ (l + 1))
    (hprot : p ^ l ∣ v s)
    (hRs : runningMax u s < H)
    (hrec : ∀ n, s ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 2) :
    ∀ n, s ≤ n → u n < H := by
  sorry

/-- A large odd prime power above `3 * R` supplies an odd multiple of `p`
that is both above `R` and below the protection height
`2 * p ^ (l + 1) / 3`. -/
theorem exists_oddMultiple_trapHeight
    {p l R : ℕ} (hp2 : 2 ≤ p) (hpodd : Odd p) (hl : 1 ≤ l)
    (hbig : 3 * R < p ^ l) :
    ∃ H, Odd H ∧ p ∣ H ∧ R < H ∧ 3 * H < 2 * p ^ (l + 1) := by
  sorry

/-- The odd cut, fed by a prime power above `3 * runningMax u s`. -/
theorem numerator_bounded_of_oddPrimePower
    (a u v w hc : ℕ → ℕ) (p l s : ℕ)
    (hp : p.Prime)
    (hpodd : Odd p)
    (hl : 1 ≤ l)
    (hred : ∀ n, s ≤ n → Nat.Coprime (u n) (v n))
    (hvpos : ∀ n, s ≤ n → 0 < v n)
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, s ≤ n → a n * v n = hc n * v (n + 1))
    (hslow : ∀ n, s ≤ n → 2 * w n ≤ 3 * u n)
    (hprot : p ^ l ∣ v s)
    (hbig : 3 * runningMax u s < p ^ l)
    (hrec : ∀ n, s ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 2) :
    ∃ H, ∀ n, s ≤ n → u n < H := by
  sorry

/-- Under the nearest-integer normalisation, a vanishing centred error
forces `u = 1` and `w = 1`, hence `u' = 1` and `hc = 1`. -/
theorem centeredZero_forces_unit
    {a u v w hc u' : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hzero : (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ) = 0) :
    u = 1 ∧ w = 1 ∧ hc = 1 ∧ u' = 1 := by
  sorry

/-- Two consecutive vanishing centred errors pin the Sylvester step. -/
theorem sylvesterStep_of_centeredZero_pair
    {a a' u v w hc u' v' : ℕ}
    (hcop : Nat.Coprime u v)
    (hq : w + v = a * u)
    (hnum : w = hc * u')
    (hden : a * v = hc * v')
    (hzero : (v : ℤ) - ((a : ℤ) - 1) * (u : ℤ) = 0)
    (hzero' : (v' : ℤ) - ((a' : ℤ) - 1) * (u' : ℤ) = 0) :
    (a' : ℤ) = sylvesterNext (a : ℤ) := by
  sorry

/-- **Record-jump rigidity, conditional on the fresh odd prime-power
supply.** Along a dynamically reduced primitive reciprocal tail with
arbitrary cancellation, if the nearest-integer normalisation holds
eventually, the normalised error vanishes, every record-setting step
rises by at most `2`, and fresh odd prime powers recur at arbitrarily
late indices dominating three times the current record, then the
multipliers eventually satisfy the exact Sylvester recurrence. -/
theorem recordRiseTwo_sylvesterNext_eventually
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (N : ℕ)
    (hvpos : ∀ n, N ≤ n → 0 < v n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, N ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, N ≤ n → 0 < w n)
    (hnum : ∀ n, N ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, N ≤ n → a n * v n = hc n * v (n + 1))
    (he : ∀ n, N ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hcentre : ∀ n, N ≤ n → 2 * (e n).natAbs < u n)
    (hvanish : ∀ K, ∃ M, ∀ n, M ≤ n → K * (e n).natAbs < u n)
    (hrec : ∀ n, N ≤ n → runningMax u n < u (n + 1) → u (n + 1) ≤ u n + 2)
    (hsupply : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ Odd p ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ 3 * runningMax u s < p ^ l) :
    ∃ M, ∀ n, M ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  sorry

end Erdos249257.ExternalVerification243PrimitiveRecordRigidity
