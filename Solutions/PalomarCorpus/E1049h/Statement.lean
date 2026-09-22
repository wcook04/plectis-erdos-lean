/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049h

Every non-theorem declaration of `PalomarCorpus/E1049h/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1049.PaperStatementsH
