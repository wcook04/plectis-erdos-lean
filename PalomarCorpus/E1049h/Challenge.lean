/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1049, band h

Erdős problem #1049 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1049` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators

namespace PalomarCorpus.E1049.PaperStatementsH
open scoped BigOperators
/-- Local copy of ErdosProblems.Erdos1049.AllRow.S, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev S := PowerSeries ℤ
/-- A finite ratio with constant term one in the state variable. Local copy of ErdosProblems.Erdos1049.AllRow.finiteRatio, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def finiteRatio (a : ℕ → S) (K n : ℕ) : S :=
  1 + ∑ s ∈ Finset.range K,
    a (s + 1) * PowerSeries.X ^ ((n + 1) * (s + 1))
/-- `H(q^{n+1}) = 1 + ∑_{s ≥ 1} a_s(q) q^{(n+1)s}`, the untruncated ratio. Each coefficient is the corresponding coefficient of a long enough truncation, which is exactly what the infinite sum means: the term of index `s` has order at least `s + 1`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperRatio, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperRatio (a : ℕ → S) (n : ℕ) : S :=
  PowerSeries.mk fun d => PowerSeries.coeff d (finiteRatio a (d + 1) n)
/-- `H̄ = H mod q`, an ordinary power series in `X` over `ℤ`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperReducedSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReducedSeries (a : ℕ → S) : PowerSeries ℤ :=
  PowerSeries.mk fun s => if s = 0 then 1 else PowerSeries.constantCoeff (a s)
/-- `h_r = [X^r] H̄(X)^{-1}`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperReciprocal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperReciprocal (a : ℕ → S) (r : ℕ) : ℤ :=
  PowerSeries.coeff r (PowerSeries.invOfUnit (paperReducedSeries a) 1)
/-- `∏_{r=1}^{m} H(q^r)`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperUnit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperUnit (a : ℕ → S) : ℕ → S
  | 0 => 1
  | n + 1 => paperUnit a n * paperRatio a n
/-- `W_m(t) = q^{(m+1)t} ∏_{r=1}^{m} H(q^r)`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.paperTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperTail (a : ℕ → S) (n t : ℕ) : S :=
  PowerSeries.X ^ ((n + 1) * t) * paperUnit a n
/-- Gaussian binomial coefficients as integer power series, using the standard Pascal recurrence. This is the coefficient occurring in Zudilin's displayed operator `D_j=(N;q)_j`. Local copy of ErdosProblems.Erdos1049.zudilinQBinomialPS, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinQBinomialPS : ℕ → ℕ → PowerSeries ℤ
  | 0, 0 => 1
  | 0, _ + 1 => 0
  | _ + 1, 0 => 1
  | n + 1, k + 1 => zudilinQBinomialPS n (k + 1) +
      PowerSeries.X ^ (n - k) * zudilinQBinomialPS n k
/-- Coefficient of the `k`th backward shift in the source operator `D_j=(N;q)_j`: `(-1)^k q^(k(k-1)/2) [j choose k]_q`. Local copy of ErdosProblems.Erdos1049.zudilinBackwardShiftCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinBackwardShiftCoeff (j k : ℕ) : PowerSeries ℤ :=
  PowerSeries.C ((-1 : ℤ) ^ k) *
    PowerSeries.X ^ (k * (k - 1) / 2) * zudilinQBinomialPS j k
/-- Apply the source operator `D_j` to the `n`th term of an arbitrary power-series sequence. The range is finite and agrees literally with the displayed Gaussian-binomial expansion in Zudilin's source. Local copy of ErdosProblems.Erdos1049.zudilinBackwardShiftApply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinBackwardShiftApply
    (j n : ℕ) (v : ℕ → PowerSeries ℤ) : PowerSeries ℤ :=
  ∑ k ∈ Finset.range (j + 1),
    zudilinBackwardShiftCoeff j k * v (n - k)
/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
  sorry
/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem all_row_initial_dvd (a : ℕ → S) (m j t : ℕ) (hjm : j ≤ m) :
    (PowerSeries.X : S) ^ (m * j - j * (j - 1) / 2) ∣
      zudilinBackwardShiftApply j m (fun n => paperTail a n t) := by
  sorry
/-- States long1049:res:allrowinitial from the long record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.all_row_initial_reciprocal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem all_row_initial_reciprocal (a : ℕ → S) (m j t : ℕ) (hjm : j ≤ m) :
    (∀ d, d < m * j - j * (j - 1) / 2 →
        PowerSeries.coeff d
          (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) = 0) ∧
      PowerSeries.coeff (m * j - j * (j - 1) / 2)
        (zudilinBackwardShiftApply j m (fun n => paperTail a n t)) =
        (if t ≤ j then (-1 : ℤ) ^ j * paperReciprocal a (j - t) else 0) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsH
