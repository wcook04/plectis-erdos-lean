/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.TotientTailPeriodKiller
import ErdosProblems.Erdos249.PaperCompleteR21.TailCarryPeriodAndRankFloor
import Solutions.PalomarCorpus.E249bc.Statement

open Filter
open Set
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStatementsBC

theorem carryShift_dvd_iff_tailDiff_integral {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N
      ↔ ∃ z : ℤ, (z : ℝ) = totientTail (N + k) - totientTail N := @ErdosProblems.Erdos249.PaperCompleteR21.carryShift_dvd_iff_tailDiff_integral v u hv hu N k

theorem temperedCarry_eq_scaledTail_and_shift {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    ((u N : ℤ) : ℝ) = (v : ℝ) * totientTail N
      ∧ ((u (N + k) - u N : ℤ) : ℝ)
          = (v : ℝ) * (totientTail (N + k) - totientTail N) := @ErdosProblems.Erdos249.PaperCompleteR21.temperedCarry_eq_scaledTail_and_shift v u hu N k

end PalomarCorpus.E249.PaperStatementsBC
