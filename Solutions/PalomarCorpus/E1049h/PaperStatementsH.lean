/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.AdelicHeightBridge
import ErdosProblems.Erdos1049.AllRow.Filtered
import ErdosProblems.Erdos1049.AllRow.FiniteStates
import ErdosProblems.Erdos1049.PaperCompleteR21.AllRowInitialCoefficient
import Solutions.PalomarCorpus.E1049h.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsH

theorem all_row_initial (a : ℕ → S) (h : ℕ → ℤ) (hzero : h 0 = 1)
    (hrec : ∀ i : ℕ, h (i + 1) =
      -(∑ s ∈ Finset.range (i + 1),
          PowerSeries.constantCoeff (a (s + 1)) * h (i - s)))
    (m j t : ℕ) (hjm : j ≤ m) :
    (∀ d, d < m * j - j * (j - 1) / 2 →
        PowerSeries.coeff d
          (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) = 0) ∧
      PowerSeries.coeff (m * j - j * (j - 1) / 2)
        (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) =
        (if t ≤ j then (-1 : ℤ) ^ j * h (j - t) else 0) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial a h hzero hrec m j t hjm

theorem all_row_initial_dvd (a : ℕ → S) (m j t : ℕ) (hjm : j ≤ m) :
    (PowerSeries.X : S) ^ (m * j - j * (j - 1) / 2) ∣
      zudilinBackwardShiftApply j m (fun n => paperTail a n t) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial_dvd a m j t hjm

theorem all_row_initial_reciprocal (a : ℕ → S) (m j t : ℕ) (hjm : j ≤ m) :
    (∀ d, d < m * j - j * (j - 1) / 2 →
        PowerSeries.coeff d
          (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) = 0) ∧
      PowerSeries.coeff (m * j - j * (j - 1) / 2)
        (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) =
        (if t ≤ j then (-1 : ℤ) ^ j * paperReciprocal a (j - t) else 0) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial_reciprocal a m j t hjm

end PalomarCorpus.E1049.PaperStatementsH
