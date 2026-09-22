/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1049j

Every non-theorem declaration of `PalomarCorpus/E1049j/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open scoped Topology
open scoped BigOperators

namespace PalomarCorpus.E1049.PaperStatementsJ
open Filter
open scoped Topology
open scoped BigOperators
/-- `C₁ = (α₀+α₁+α₂)β - (α₁²+α₂²+β²)/2 = 1091/2`, Zudilin's (25). Local copy of ErdosProblems.Erdos1049.zudilinC1, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinC1 : ℝ := 1091 / 2
/-- The series representation of the trigamma function. Only this series is used; the identification with `d²/dx² log Γ` is classical and not needed. Local copy of ErdosProblems.Erdos1049.trigammaSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def trigammaSeries (x : ℝ) : ℝ := ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2
/-- One interval's contribution `ψ₁(u) - ψ₁(v)`. Local copy of ErdosProblems.Erdos1049.zudilinJTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinJTerm (u v : ℝ) : ℝ := trigammaSeries u - trigammaSeries v
/-- `J = ∫₀¹ ω(x) d(-ψ'(x))` over the thirteen intervals on which `ω = 1` (Zudilin 2004, end of Section 5), written as the trigamma series. Local copy of ErdosProblems.Erdos1049.zudilinJ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)
/-- `C₀ = α₁²/2 + α₀α₁ + (β-α₂)(α₂-α₁) - (3/π²)(m² - J)` with `m = 15`, Zudilin's (26). Local copy of ErdosProblems.Erdos1049.zudilinC0, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)
/-- `μ = C₁/C₀`, the reciprocal of the contour `θ* = C₀/C₁`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinMu : ℝ := zudilinC1 / zudilinC0
/-- Precisely the real Lambert value in the paper, indexed from exponent one. Outside x > 1 this is still Lean's totalised sum; none of the target statements uses those other inputs. Summability is a separate analytic obligation. Local copy of ErdosProblems.Erdos1049.PaperR7.paperLambert, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)
/-- The rational-base threshold `θ* = C₀/C₁ = 1/μ`, where `μ = C₁/C₀` is the irrationality-exponent bound of Zudilin's Theorem 1. Local copy of ErdosProblems.Erdos1049.zudilinContour, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1
end PalomarCorpus.E1049.PaperStatementsJ
