/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.PaperCompleteR20.RealBaseShortInterval
import ErdosProblems.Erdos269.PaperCompleteR20.RealTwoPrimeKernel
import ErdosProblems.Erdos269.ResidueEscape
import Solutions.PalomarCorpus.E269b.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStatementsB

theorem exponent_unique_real_base_short_interval
    {base lo hi weight : ℝ} {a b : ℕ}
    (hbase : 1 ≤ base) (hweight : 0 ≤ weight)
    (hwidth : hi ≤ base * lo)
    (haLo : lo ≤ base ^ a * weight) (haHi : base ^ a * weight < hi)
    (hbLo : lo ≤ base ^ b * weight) (hbHi : base ^ b * weight < hi) :
    a = b := @ErdosProblems.Erdos269.PaperCompleteR20.exponent_unique_real_base_short_interval base lo hi weight a b hbase hweight hwidth haLo haHi hbLo hbHi

theorem real_two_prime_separation {p q : ℝ} (hp : 1 < p) (hq : 1 < q) :
    (∀ i j : ℕ, realTwoPrimeKernel p q i j =
      (p ^ i * q ^ ⌊Real.logb q (p ^ i)⌋)⁻¹ *
        (p ^ ⌊Real.logb p (q ^ j)⌋ * q ^ j)⁻¹) ∧
    (∀ i i' j j' : ℕ,
      realTwoPrimeKernel p q i j * realTwoPrimeKernel p q i' j' -
        realTwoPrimeKernel p q i j' * realTwoPrimeKernel p q i' j = 0) := @ErdosProblems.Erdos269.PaperCompleteR20.real_two_prime_separation p q hp hq

theorem no_bounded_positive_int_state_of_leastPositiveResidue
    {C bound : ℕ} {x c : ℤ}
    (hC : 0 < C)
    (hcpos : 0 < c)
    (hcbound : Int.natAbs c ≤ bound)
    (hescape : bound < leastPositiveResidue C x)
    (hmod : Int.ModEq C c x) :
    False := @ErdosProblems.Erdos269.no_bounded_positive_int_state_of_leastPositiveResidue C bound x c hC hcpos hcbound hescape hmod

end PalomarCorpus.E269.PaperStatementsB
