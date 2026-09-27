/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos243.PaperCompleteR21.DoubleLogOrbitBound

/-!
Exact-statement compile probe for the arbitrary-orbit inclusive double-log bound.
The source theorem is copied without changes from plectis-erdos commit
551bae6dc6e732cf85172d66323c8d2bc77ba962. This module enters the existing
Solutions.+ default build. It adds no Comparator or Palomar entry.

The positive probe retains every hypothesis and the EReal limsup at coefficient
one. The negative control checks that the source theorem cannot be used without
the limsup premise; it is a type-check control, not a counterexample theorem.
Successful elaboration and printed axioms must be read from the exact CI run.
-/

open Filter

example
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (h1 : ∀ n, 1 < a n ∧ 0 < C n)
    (h2 : ∀ n, C (n + 1) + D n = a n * C n ∧ D (n + 1) = a n * D n)
    (h3 : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ))
    (_h4 : ∃ N, ∀ n, N ≤ n → |E n| < (C n : ℤ))
    (h6 : ∀ K : ℤ, 1 ≤ K → ∃ N, ∀ n, N ≤ n → K * |E n| < (C n : ℤ)) :
    limsup (fun n => ((((max (-E n) 0 : ℤ) : ℝ) /
        Real.logb 2 (Real.logb 2 (max 4 (C n : ℝ))) : ℝ) : EReal)) atTop ≤ 1 →
      ∃ N, ∀ n, N ≤ n → E n = 0 := by
  exact ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_double_logarithmic_bound
    a C D E h1 h2 h3 _h4 h6

example
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (h1 : ∀ n, 1 < a n ∧ 0 < C n)
    (h2 : ∀ n, C (n + 1) + D n = a n * C n ∧ D (n + 1) = a n * D n)
    (h3 : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ))
    (_h4 : ∃ N, ∀ n, N ≤ n → |E n| < (C n : ℤ))
    (h6 : ∀ K : ℤ, 1 ≤ K → ∃ N, ∀ n, N ≤ n → K * |E n| < (C n : ℤ)) : True := by
  fail_if_success
    have wrong : ∃ N, ∀ n, N ≤ n → E n = 0 := by
      exact ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_double_logarithmic_bound
        a C D E h1 h2 h3 _h4 h6
  trivial

#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_double_logarithmic_bound
#print axioms ErdosProblems.Erdos243.PaperCompleteR21.exactOrbit_recordTheta_gt_one
#print axioms ErdosProblems.Erdos243.PaperCompleteR11.recordTheta_le_negativeError_limsup
