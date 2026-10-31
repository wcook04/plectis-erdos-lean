/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1049, note sections 2 to 4: a region of rational bases at which F is irrational; supplementary arithmetic at 3/2

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1049, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #1049 remains open, and no theorem
in this entry decides it.
-/

open scoped BigOperators
open Filter
open Asymptotics
open scoped Topology
open Polynomial

namespace PalomarCorpus.E1049.PaperStatementsA
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
/-- `μ = C₁/C₀`, the irrationality-exponent constant printed in the theorem. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.paperMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperMu : ℝ := zudilinC1 / zudilinC0
/-- Numerator of the Euler-Maclaurin tail over `2310 x¹¹`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailNum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailNum (x : ℝ) : ℝ :=
  2310 * x ^ 10 + 1155 * x ^ 9 + 385 * x ^ 8 - 77 * x ^ 6 + 55 * x ^ 4 - 77 * x ^ 2
/-- `tailLow x + 5/(66x¹¹)`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailHigh, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailHigh (x : ℝ) : ℝ := (tailNum x + 175) / (2310 * x ^ 11)
/-- `1/x + 1/(2x²) + 1/(6x³) - 1/(30x⁵) + 1/(42x⁷) - 1/(30x⁹)`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tailLow (x : ℝ) : ℝ := tailNum x / (2310 * x ^ 11)
/-- `μ = C₁/C₀`, the reciprocal of the contour `θ* = C₀/C₁`. Local copy of ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinMu : ℝ := zudilinC1 / zudilinC0
/-- The rational-base threshold `θ* = C₀/C₁ = 1/μ`, where `μ = C₁/C₀` is the irrationality-exponent bound of Zudilin's Theorem 1. Local copy of ErdosProblems.Erdos1049.zudilinContour, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_contour_short in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_contour_short :
    (4056830213840605 : ℝ) / 10 ^ 16 < zudilinContour ∧
      zudilinContour < (4056830213840606 : ℝ) / 10 ^ 16 := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.printed_mu in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem printed_mu :
    (24649786835749750 : ℝ) / 10 ^ 16 < paperMu ∧
      paperMu < (24649786835749751 : ℝ) / 10 ^ 16 := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.tailLow_le_trigammaSeries in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailLow_le_trigammaSeries {x : ℝ} (hx : 1 ≤ x) : tailLow x ≤ trigammaSeries x := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.PrintedContour.trigammaSeries_le_tailHigh in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem trigammaSeries_le_tailHigh {x : ℝ} (hx : 1 ≤ x) : trigammaSeries x ≤ tailHigh x := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.zudilinContour_eq_inv_mu in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem zudilinContour_eq_inv_mu : zudilinContour = 1 / zudilinMu := by
  sorry
/-- States res:rational-base-threshold from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.zudilinMu_mul_zudilinContour in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem zudilinMu_mul_zudilinContour : zudilinMu * zudilinContour = 1 := by
  sorry
end PalomarCorpus.E1049.PaperStatementsA

namespace PalomarCorpus.E1049.RationalBaseRegion
open scoped BigOperators
/-- The real Lambert series F(x)=sum over n at least 1 of 1/(x^n-1), with Lean tsum conventions outside its convergence domain; the irrationality theorems use x>1. -/
noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)
/-- The Lambert value at every positive integral power of 31/4 is irrational, by the constructed-source contour theorem. -/
theorem thirtyone_four_powers (r : ℕ) (hr : 0 < r) :
    Irrational (paperLambert (((31 : ℝ) / 4) ^ r)) := by
  sorry
end PalomarCorpus.E1049.RationalBaseRegion

namespace PalomarCorpus.E1049.PaperStructuresR
open Filter
open Asymptotics
open scoped Topology
open scoped BigOperators
/-- Local definition coeffL1, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def coeffL1 (P : Polynomial ℤ) : ℝ :=
  ∑ i ∈ P.support, |(P.coeff i : ℝ)|
/-- Local copy of ErdosProblems.Erdos1049.PaperR9.pairWidth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def pairWidth (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ :=
  max (U n).natDegree (V n).natDegree
/-- Local copy of ErdosProblems.Erdos1049.PaperR9.polynomialRemainder, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialRemainder (U V : ℕ → Polynomial ℤ)
    (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x -
    (V n).eval₂ (Int.castRingHom ℝ) x
/-- Local definition pairHeight, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pairHeight (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℝ :=
  max (coeffL1 (U n)) (coeffL1 (V n))
/-- The scale is a real square, avoiding truncated natural subtraction. Local copy of ErdosProblems.Erdos1049.PaperR9.sqScale, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sqScale (n : ℕ) : ℝ := (n : ℝ) ^ 2
/-- Upper quadratic rate, with an arbitrary additive epsilon in the rate. Local copy of ErdosProblems.Erdos1049.PaperR9.QuadUpper, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def QuadUpper (f : ℕ → ℝ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, f n ≤ (a + ε) * sqScale n
/-- Exact two-sided logarithmic asymptotic; nonvanishing is supplied separately. Local copy of ErdosProblems.Erdos1049.PaperR9.QuadLogRate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def QuadLogRate (f : ℕ → ℝ) (a : ℝ) : Prop :=
  (fun n => Real.log |f n| - a * sqScale n) =o[atTop] sqScale
/-- Local definition CapHypotheses, copied so the compared statements of this entry elaborate against Mathlib alone. -/
structure CapHypotheses (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) : Prop where
  sigma_pos : 0 < σ
  delta_pos : 0 < δ
  height_nonneg : 0 ≤ h
  degree_upper : QuadUpper (fun n => (pairWidth U V n : ℝ)) δ
  height_upper : QuadUpper (fun n => Real.log (pairHeight U V n)) h
  nonzero : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, polynomialRemainder U V F x n ≠ 0
  remainder_rate : ∀ x : ℝ, 1 < x →
    QuadLogRate (polynomialRemainder U V F x) (-σ * Real.log x)
/-- States res:archimedean-cap from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperR9.short_note_archimedean_cap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem short_note_archimedean_cap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ)
    (σ δ h : ℝ) (H : CapHypotheses U V F σ δ h) :
    σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    ∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
      Tendsto (fun n => (b : ℝ) ^ pairWidth U V n *
        polynomialRemainder U V F ((a : ℝ) / b) n) atTop (𝓝 0) := by
  sorry
end PalomarCorpus.E1049.PaperStructuresR

namespace PalomarCorpus.E1049.PaperStatementsF
open Polynomial
/-- Integer homogeneous evaluation of an integral polynomial at `(3,2)`, using the declared ambient width `W`. Local copy of ErdosProblems.Erdos1049.homEvalThreeTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def homEvalThreeTwo (W : ℕ) (P : Polynomial ℤ) : ℤ :=
  ∑ i ∈ Finset.range (W + 1), P.coeff i * 3 ^ i * 2 ^ (W - i)
/-- The bottom `3`-adic endpoint jet of depth `R`. Local copy of ErdosProblems.Erdos1049.bottomJet3, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def bottomJet3 (R W : ℕ) (P : Polynomial ℤ) : ZMod (3 ^ R) :=
  homEvalThreeTwo W P
/-- States res:bottomjet from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.bottomJet3_eq_zero_iff_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bottomJet3_eq_zero_iff_dvd (R W : ℕ) (P : Polynomial ℤ) :
    bottomJet3 R W P = 0 ↔ ((3 ^ R : ℕ) : ℤ) ∣ homEvalThreeTwo W P := by
  sorry
end PalomarCorpus.E1049.PaperStatementsF

namespace PalomarCorpus.E1049.PaperStructuresP
/-- Local definition instDecidableEqReal_erdosProblems, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable scoped instance instDecidableEqReal_erdosProblems : DecidableEq ℝ := Classical.decEq ℝ
/-- States res:boundedfibre from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.exists_small_real_escape_of_conditional_multiplicity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_small_real_escape_of_conditional_multiplicity
    {α β ι : Type*}
    [Fintype α] [Fintype β] [Fintype ι]
    [DecidableEq α] [DecidableEq β] [DecidableEq ι]
    (f : α → β) (g : α → ℝ) (bin : α → ι) (k : ℕ) (δ : ℝ)
    (hg : ∀ x : α,
      (Finset.univ.filter fun y => f y = f x ∧ g y = g x).card ≤ k)
    (hdiam : ∀ x y : α, bin x = bin y → |g x - g y| < δ)
    (hcard : (Fintype.card β * Fintype.card ι) * k < Fintype.card α) :
    ∃ x y : α, x ≠ y ∧ f x = f y ∧
      0 < |g x - g y| ∧ |g x - g y| < δ := by
  sorry
end PalomarCorpus.E1049.PaperStructuresP
