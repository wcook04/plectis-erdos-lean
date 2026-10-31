/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.MersenneLambertLadder
import Erdos249257.TotientShiftedMobiusPulse
import ErdosProblems.Erdos249.PaperCompleteR21.LambertDivisorTransform
import ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion
import Solutions.PalomarCorpus.E249_08.Statement

open scoped BigOperators
open ArithmeticFunction

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsBA
export PalomarCorpus.E249_08.Shared (lambertValue)

noncomputable def forwardMultipleQuotient (N d : ℕ) : ℕ := N / d + 1

noncomputable def forwardMultipleShift (N d : ℕ) : ℕ := d - N % d

theorem alpha_divisor_sum_eq_totient (n : ℕ) :
    ∑ e ∈ n.divisors, ((primWeight e : ℤ) : ℝ) = (Nat.totient n : ℝ) := @ErdosProblems.Erdos249.PaperCompleteR21.alpha_divisor_sum_eq_totient n

theorem forwardMultipleShift_least (N : ℕ) {d m : ℕ} (hd : 0 < d) (hm : 0 < m)
    (hlt : m < forwardMultipleShift N d) : ¬ d ∣ N + m := @ErdosProblems.Erdos249.PaperCompleteR21.forwardMultipleShift_least N d m hd hm hlt

theorem forwardMultiple_enumeration (N : ℕ) {d : ℕ} (hd : 0 < d) (l : ℕ) :
    N + (forwardMultipleShift N d + d * l) =
      d * (forwardMultipleQuotient N d + l) := @ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_enumeration N d hd l

theorem forwardMultiple_spec (N : ℕ) {d : ℕ} (hd : 0 < d) :
    forwardMultipleShift N d = d - N % d ∧
      forwardMultipleQuotient N d = N / d + 1 ∧
      1 ≤ forwardMultipleShift N d ∧
      forwardMultipleShift N d ≤ d ∧
      d ∣ N + forwardMultipleShift N d := @ErdosProblems.Erdos249.PaperCompleteR21.forwardMultiple_spec N d hd

theorem lambertValue_alpha_eq_totientSeries :
    lambertValue (fun d => ((primWeight d : ℤ) : ℝ))
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := @ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_alpha_eq_totientSeries

end PalomarCorpus.E249.PaperStatementsBA
