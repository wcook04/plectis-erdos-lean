/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.PaperCompleteR21.TwoPrimeSums
import Solutions.PalomarCorpus.E269x.Statement

open Polynomial
open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStatementsX

theorem two_prime_sums_transcendental (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p < q) :
    Transcendental ℚ (distinctSum p q) ∧ Transcendental ℚ (repeatedSum p q) := @ErdosProblems.Erdos269.PaperCompleteR21.two_prime_sums_transcendental hBL p q hp hq hpq

theorem two_prime_transcendence (hBL : BugeaudLaurentTranscendence)
    {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    Transcendental ℚ (repeatedSum p q) ∧ Transcendental ℚ (distinctSum p q) := @ErdosProblems.Erdos269.PaperCompleteR21.two_prime_transcendence hBL p q hp hq hpq

end PalomarCorpus.E269.PaperStatementsX
