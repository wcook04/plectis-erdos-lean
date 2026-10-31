/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.SaturatedSquareTransport
import Solutions.PalomarCorpus.E243_11.Statement

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E243.RecordAmplifiedCancellationVisibility
export PalomarCorpus.E243_11.Shared (runningMax)

theorem runningMax_eq (u : ℕ → ℕ) :
    ∀ n, runningMax u n = ErdosProblems.Erdos243.runningMax u n
  | 0 => rfl
  | n + 1 => by
    simp only [runningMax, ErdosProblems.Erdos243.runningMax, runningMax_eq]

theorem recordAmplified_error_after_cancellation
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (s t : ℕ)
    (hst : s + 1 ≤ t)
    (he : ∀ n, s ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hw : ∀ n, s ≤ n → w n + v n = a n * u n)
    (hnum : ∀ n, s ≤ n → w n = hc n * u (n + 1))
    (hwpos : ∀ n, s ≤ n → 0 < w n)
    (hnonneg : ∀ j, s < j → j < t → 0 ≤ e j)
    (hneg : e t < 0) :
    u t ≤ u (s + 1) ∧
      u s * u t ≤ runningMax u t * (e t).natAbs * u (s + 1) := by
  simpa only [runningMax_eq] using
    ErdosProblems.Erdos243.recordAmplified_error_after_cancellation
      a u v w hc e s t hst he hw hnum hwpos hnonneg hneg

end PalomarCorpus.E243.RecordAmplifiedCancellationVisibility
