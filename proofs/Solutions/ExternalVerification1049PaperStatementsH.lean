/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1049.AdelicHeightBridge
import ErdosProblems.Erdos1049.AllRow.Filtered
import ErdosProblems.Erdos1049.AllRow.FiniteStates
import ErdosProblems.Erdos1049.PaperCompleteR21.AllRowInitialCoefficient

/-!
# Independent restatements for Erdős problem #1049

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1049.AdelicHeightBridge`, `ErdosProblems.Erdos1049.AllRow.Filtered`,
`ErdosProblems.Erdos1049.AllRow.FiniteStates`,
`ErdosProblems.Erdos1049.PaperCompleteR21.AllRowInitialCoefficient`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification1049PaperStatementsH

noncomputable abbrev S := PowerSeries ℤ

noncomputable def finiteRatio (a : ℕ → S) (K n : ℕ) : S :=
  1 + ∑ s ∈ Finset.range K,
    a (s + 1) * PowerSeries.X ^ ((n + 1) * (s + 1))

noncomputable def paperRatio (a : ℕ → S) (n : ℕ) : S :=
  PowerSeries.mk fun d => PowerSeries.coeff d (finiteRatio a (d + 1) n)

noncomputable def paperReducedSeries (a : ℕ → S) : PowerSeries ℤ :=
  PowerSeries.mk fun s => if s = 0 then 1 else PowerSeries.constantCoeff (a s)

noncomputable def paperReciprocal (a : ℕ → S) (r : ℕ) : ℤ :=
  PowerSeries.coeff r (PowerSeries.invOfUnit (paperReducedSeries a) 1)

noncomputable def paperUnit (a : ℕ → S) : ℕ → S
  | 0 => 1
  | n + 1 => paperUnit a n * paperRatio a n

noncomputable def paperTail (a : ℕ → S) (n t : ℕ) : S :=
  PowerSeries.X ^ ((n + 1) * t) * paperUnit a n

noncomputable def zudilinQBinomialPS : ℕ → ℕ → PowerSeries ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => zudilinQBinomialPS n (k + 1) +
      PowerSeries.X ^ (n - k) * zudilinQBinomialPS n k

noncomputable def zudilinBackwardShiftCoeff (j k : ℕ) : PowerSeries ℤ :=
  PowerSeries.C ((-1 : ℤ) ^ k) *
    PowerSeries.X ^ (k * (k - 1) / 2) * zudilinQBinomialPS j k

noncomputable def zudilinBackwardShiftApply
    (j n : ℕ) (v : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range (j + 1),
    zudilinBackwardShiftCoeff j k * v (n - k)

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

end Erdos249257.ExternalVerification1049PaperStatementsH
