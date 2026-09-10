/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos249.PrefixValuationAndControlRigidity

/-!
# Source transport for the prefix 2-adic denominator exclusion in Erdős #249
-/

namespace Erdos249257.ExternalVerification249PrefixTwoAdicExclusion

set_option linter.unusedVariables false

def totientPrefix (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * Nat.totient (i + 1)

theorem totientPrefix_succ (n : ℕ) :
    totientPrefix (n + 1) = 2 * totientPrefix n + Nat.totient (n + 1) := by
  simpa [totientPrefix, ErdosProblems.Erdos249.totientPrefix] using
    ErdosProblems.Erdos249.totientPrefix_succ n

theorem totientPrefix_eq_corpusForm (n : ℕ) :
    totientPrefix n = ∑ i ∈ Finset.range (n + 1), Nat.totient i * 2 ^ (n - i) := by
  simpa [totientPrefix, ErdosProblems.Erdos249.totientPrefix] using
    ErdosProblems.Erdos249.totientPrefix_eq_corpusForm n

noncomputable def prefixTail (S : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * S - (totientPrefix n : ℝ)

theorem oddPart_mul_prefixTail_eq_intCast
    {S : ℝ} {a : ℤ} {c v n : ℕ} (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hcn : c ≤ n) :
    (v : ℝ) * prefixTail S n
      = (((2 : ℤ) ^ (n - c) * a - (v : ℤ) * (totientPrefix n : ℤ) : ℤ) : ℝ) := by
  simpa [totientPrefix, prefixTail, ErdosProblems.Erdos249.totientPrefix,
      ErdosProblems.Erdos249.prefixTail] using
    ErdosProblems.Erdos249.oddPart_mul_prefixTail_eq_intCast hvpos hS hcn

theorem prefix_twoAdic_denominator_exclusion
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * prefixTail S n := by
  simpa [totientPrefix, prefixTail, ErdosProblems.Erdos249.totientPrefix,
      ErdosProblems.Erdos249.prefixTail] using
    ErdosProblems.Erdos249.prefix_twoAdic_denominator_exclusion hvodd hvpos hS hpos hct hdvd

theorem prefix_twoAdic_denominator_lower_bound
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * ((n : ℝ) + 2) := by
  simpa [totientPrefix, prefixTail, ErdosProblems.Erdos249.totientPrefix,
      ErdosProblems.Erdos249.prefixTail] using
    ErdosProblems.Erdos249.prefix_twoAdic_denominator_lower_bound
      hvodd hvpos hS hpos htail hct hdvd

theorem prefix_twoAdic_odd_denominator_floor
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t / ((n : ℝ) + 2) ≤ (v : ℝ) := by
  simpa [totientPrefix, prefixTail, ErdosProblems.Erdos249.totientPrefix,
      ErdosProblems.Erdos249.prefixTail] using
    ErdosProblems.Erdos249.prefix_twoAdic_odd_denominator_floor
      hvodd hvpos hS hpos htail hct hdvd

end Erdos249257.ExternalVerification249PrefixTwoAdicExclusion
