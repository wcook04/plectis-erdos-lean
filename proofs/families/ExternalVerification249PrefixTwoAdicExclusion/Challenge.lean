/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib

/-!
# Trusted challenge for the prefix 2-adic denominator exclusion in Erdős #249

A single 2-adic valuation of the totient prefix integer excludes a rectangle
of candidate denominators `2^c v`. This is a finite exclusion for rational
representations of a real `S`, not irrationality of the binary totient series.
Erdős #249 remains open.
-/

namespace Erdos249257.ExternalVerification249PrefixTwoAdicExclusion

set_option linter.unusedVariables false

/-- The integer prefix `P_n = ∑_{i<n} 2^{n-1-i} φ(i+1)` of `2ⁿ·S`. -/
def totientPrefix (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * Nat.totient (i + 1)

/-- The defining recurrence `P_{n+1} = 2 P_n + φ(n+1)`. -/
theorem totientPrefix_succ (n : ℕ) :
    totientPrefix (n + 1) = 2 * totientPrefix n + Nat.totient (n + 1) := by
  sorry

/-- Correspondence with the shared prefix `∑_{i ≤ n} φ(i) 2^{n-i}`. -/
theorem totientPrefix_eq_corpusForm (n : ℕ) :
    totientPrefix n = ∑ i ∈ Finset.range (n + 1), Nat.totient i * 2 ^ (n - i) := by
  sorry

/-- The abstract local tail `R_n = 2ⁿ·S - P_n`. -/
noncomputable def prefixTail (S : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * S - (totientPrefix n : ℝ)

/-- Under `S = a / (2^c v)` and `c ≤ n`, the rescaled tail `v·R_n` is an integer. -/
theorem oddPart_mul_prefixTail_eq_intCast
    {S : ℝ} {a : ℤ} {c v n : ℕ} (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hcn : c ≤ n) :
    (v : ℝ) * prefixTail S n
      = (((2 : ℤ) ^ (n - c) * a - (v : ℤ) * (totientPrefix n : ℤ) : ℤ) : ℝ) := by
  sorry

/-- If `S = a/(2^c v)` with `v > 0` odd, the local tail is positive, `c + t ≤ n`,
and `2^t ∣ P_n`, then `2^t ≤ v · R_n`. -/
theorem prefix_twoAdic_denominator_exclusion
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * prefixTail S n := by
  sorry

/-- Corollary with the canonical tail bound `R_n ≤ n + 2`. -/
theorem prefix_twoAdic_denominator_lower_bound
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * ((n : ℝ) + 2) := by
  sorry

/-- The same exclusion as a lower bound on the odd part: `v ≥ 2^t / (n + 2)`. -/
theorem prefix_twoAdic_odd_denominator_floor
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t / ((n : ℝ) + 2) ≤ (v : ℝ) := by
  sorry

end Erdos249257.ExternalVerification249PrefixTwoAdicExclusion
