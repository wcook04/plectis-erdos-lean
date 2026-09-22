/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #243, band r

Erdős problem #243 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E243` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open scoped Topology

namespace PalomarCorpus.E243.PaperStatementsR
open Filter
open scoped Topology
/-- The exact real-valued normaliser from the inclusive boundary. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.recordLogLog, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recordLogLog (x : ℝ) : ℝ :=
  Real.log (Real.log (max 4 x) / Real.log 2) / Real.log 2
/-- Running maximum `R n = max_{k ≤ n} u k` of a numerator sequence. Local copy of ErdosProblems.Erdos243.runningMax, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))
/-- The paper's all-index record quotient, before passing to a limsup. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.recordLogLogCharge, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recordLogLogCharge (U : ℕ → ℕ) (n : ℕ) : ℝ :=
  ((runningMax U (n + 1) - runningMax U n : ℕ) : ℝ) / recordLogLog (runningMax U n)
/-- The exact extended-real record coefficient Theta. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.recordTheta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def recordTheta (U : ℕ → ℕ) : EReal :=
  limsup (fun n ↦ (recordLogLogCharge U n : EReal)) atTop
/-- States long243:res:strausbounded from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.recordTheta_le_of_slow_negative in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem recordTheta_le_of_slow_negative
    (a C D : ℕ → ℕ) (E : ℕ → ℤ)
    (hstep : ∀ n, C (n + 1) + D n = a n * C n)
    (hE : ∀ n, E n = (D n : ℤ) - ((a n : ℤ) - 1) * (C n : ℤ))
    (c : ℝ) (hc0 : 0 ≤ c) (N : ℕ)
    (hslow : ∀ n, N ≤ n → -((E n : ℤ) : ℝ) ≤ c * recordLogLog ((C n : ℕ) : ℝ)) :
    recordTheta C ≤ ((c : ℝ) : EReal) := by
  sorry
end PalomarCorpus.E243.PaperStatementsR
