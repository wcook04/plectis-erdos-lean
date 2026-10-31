/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos243.RecordIncrementBarrier
import Solutions.PalomarCorpus.E243_11.Statement

namespace PalomarCorpus.E243.RecordIncrementBarrier
export PalomarCorpus.E243_11.Shared (runningMax sylvesterNext)

theorem runningMax_eq (u : ℕ → ℕ) (n : ℕ) :
    runningMax u n = ErdosProblems.Erdos243.runningMax u n := by
  induction n with
  | zero => simp [runningMax, ErdosProblems.Erdos243.runningMax]
  | succ k ih => simp [runningMax, ErdosProblems.Erdos243.runningMax, ih]

theorem recordIncrementOne_sylvesterNext_eventually
    (a u v w hc : ℕ → ℕ) (e : ℕ → ℤ) (N : ℕ)
    (hvpos : ∀ n, N ≤ n → 0 < v n)
    (hred : ∀ n, N ≤ n → Nat.Coprime (u n) (v n))
    (hw : ∀ n, N ≤ n → w n + v n = a n * u n)
    (hwpos : ∀ n, N ≤ n → 0 < w n)
    (hnum : ∀ n, N ≤ n → w n = hc n * u (n + 1))
    (hden : ∀ n, N ≤ n → a n * v n = hc n * v (n + 1))
    (he : ∀ n, N ≤ n → e n = (v n : ℤ) - ((a n : ℤ) - 1) * (u n : ℤ))
    (hcentre : ∀ n, N ≤ n → 2 * (e n).natAbs < u n)
    (hvanish : ∀ K, ∃ M, ∀ n, M ≤ n → K * (e n).natAbs < u n)
    (hinc : ∀ n, N ≤ n → runningMax u (n + 1) ≤ runningMax u n + 1)
    (hsupply : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ runningMax u s + 3 ≤ p ^ l) :
    ∃ M, ∀ n, M ≤ n → (a (n + 1) : ℤ) = sylvesterNext (a n : ℤ) := by
  have hinc' : ∀ n, N ≤ n →
      ErdosProblems.Erdos243.runningMax u (n + 1)
        ≤ ErdosProblems.Erdos243.runningMax u n + 1 := by
    intro n hn
    simpa [runningMax_eq] using hinc n hn
  have hsupply' : ∀ M, ∃ s, M ≤ s ∧ ∃ p l, p.Prime ∧ 1 ≤ l ∧
      p ^ l ∣ v s ∧ ErdosProblems.Erdos243.runningMax u s + 3 ≤ p ^ l := by
    intro M
    obtain ⟨s, hMs, p, l, hp, hl, hpl, hbig⟩ := hsupply M
    exact ⟨s, hMs, p, l, hp, hl, hpl, by simpa [runningMax_eq] using hbig⟩
  simpa [sylvesterNext, ErdosProblems.Erdos243.sylvesterNext] using
    ErdosProblems.Erdos243.recordIncrementOne_sylvesterNext_eventually
      a u v w hc e N hvpos hred hw hwpos hnum hden he hcentre hvanish hinc' hsupply'

end PalomarCorpus.E243.RecordIncrementBarrier
