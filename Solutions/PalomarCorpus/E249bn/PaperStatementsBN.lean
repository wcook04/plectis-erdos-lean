/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.MersenneLambertLadder
import ErdosProblems.Erdos249.PaperCompleteR21.CompositeDilationIdentity
import Solutions.PalomarCorpus.E249bn.Statement

open ArithmeticFunction

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsBN

theorem totient_convolution_weight_mul_zeta (n : ℕ) :
    ∑ e ∈ n.divisors, primWeight e = (Nat.totient n : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_mul_zeta n

theorem totient_convolution_weight_not_periodic :
    ¬ ∃ p : ℕ, 0 < p ∧
      ∀ n : ℕ, primWeight (n + p) =
        primWeight n := @ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_not_periodic

theorem totient_convolution_weight_prime {p : ℕ} (hp : p.Prime) :
    primWeight p = (p : ℤ) - 2 := @ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_prime p hp

theorem totient_convolution_weight_unbounded :
    ¬ ∃ B : ℕ, ∀ n : ℕ, primWeight n ≤ (B : ℤ) := @ErdosProblems.Erdos249.PaperCompleteR21.totient_convolution_weight_unbounded

end PalomarCorpus.E249.PaperStatementsBN
