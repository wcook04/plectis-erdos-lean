/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos243.SaturatedSquareTransport


namespace Erdos249257.ExternalVerification243RecordAmplifiedCancellationVisibility

def runningMax (u : ℕ → ℕ) : ℕ → ℕ
  | 0 => u 0
  | n + 1 => max (runningMax u n) (u (n + 1))

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

end Erdos249257.ExternalVerification243RecordAmplifiedCancellationVisibility
