/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1041, note sections 13 to 16: two chord constructions for binomials; a Poisson identity for critical-value means; a nonlinear integral for component mergers

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1041, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. A degree-seven counterexample due to ani,
formalised in this corpus, refutes the total-variation formulation of Erdős problem
#1041; the theorems in this entry keep their stated hypotheses.
-/

open Set
open scoped ENNReal
open scoped NNReal
open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex
open Polynomial
open Finset
open Polynomial Set
open Polynomial Metric
open Filter
open MeasureTheory
open scoped Topology

namespace PalomarCorpus.E1041.PaperStatementsD
open Set
open scoped ENNReal
open scoped NNReal
/-- `π/n`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.angle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def angle (n : ℕ) : ℝ := Real.pi / (n : ℝ)
/-- `c = cos(π/n)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordCos, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordCos (n : ℕ) : ℝ := Real.cos (angle n)
/-- `ε = (1 - r^n)^{1/n}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordEps, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordEps (n : ℕ) (r : ℝ) : ℝ := (1 - r ^ n) ^ ((n : ℝ)⁻¹)
/-- `e^{iπ/n}`; its square is the paper's `ω = e^{2πi/n}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.halfRoot, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def halfRoot (n : ℕ) : ℂ := Complex.exp ((angle n : ℂ) * Complex.I)
/-- `ω = e^{2πi/n}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordOmega, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordOmega (n : ℕ) : ℂ := halfRoot n ^ 2
/-- The point of the segment `[s, sω]` at parameter `u ∈ [0,1]`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordPoint, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordPoint (n : ℕ) (s u : ℝ) : ℂ :=
  (s : ℂ) * (((1 - u : ℝ) : ℂ) + ((u : ℝ) : ℂ) * chordOmega n)
/-- `r_* = (1 + c^n)^{-1/n}`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.chordThreshold, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def chordThreshold (n : ℕ) : ℝ := (1 + chordCos n ^ n) ^ (-((n : ℝ)⁻¹))
/-- The paper's inner radius `t = ε/c`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChord.innerRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def innerRadius (n : ℕ) (r : ℝ) : ℝ := chordEps n r / chordCos n
/-- The geometric conclusion used by the paper: a continuous rectifiable curve with specified endpoints, containment at every parameter, and a strict variation bound. Local copy of ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
/-- States the paper statement it is bound to from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chord_decisive_step in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binomial_chord_decisive_step {n : ℕ} (hn : 2 ≤ n) {θ : ℝ}
    (hθ : (n : ℝ) * |θ| ≤ Real.pi) :
    1 + Real.cos ((n : ℝ) * θ) ≤ 2 * Real.cos θ ^ n := by
  sorry
/-- States the paper statement it is bound to from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chord_maximum in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binomial_chord_maximum {n : ℕ} (hn : 2 ≤ n) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n s u) ^ n - ((r : ℝ) : ℂ) ^ n‖ ≤ r ^ n + (s * chordCos n) ^ n) ∧
      ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = r ^ n + (s * chordCos n) ^ n := by
  sorry
/-- States the paper statement it is bound to from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_above_threshold in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binomial_chords_above_threshold {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hge : chordThreshold n ≤ r) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by
  sorry
/-- States the paper statement it is bound to from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_at_threshold in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binomial_chords_at_threshold {n : ℕ} (hn : 2 ≤ n) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n (chordThreshold n) u) ^ n
          - ((chordThreshold n : ℝ) : ℂ) ^ n‖ ≤ 1) ∧
      ‖(chordPoint n (chordThreshold n) (1 / 2)) ^ n
        - ((chordThreshold n : ℝ) : ℂ) ^ n‖ = 1 := by
  sorry
/-- States the paper statement it is bound to from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_below_threshold in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binomial_chords_below_threshold {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hlt : r < chordThreshold n) :
    ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by
  sorry
/-- States the paper statement it is bound to from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_path in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binomial_chords_path {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((r : ℝ) : ℂ) ≠ ((r : ℝ) : ℂ) * chordOmega n ∧
      (((r : ℝ) : ℂ)) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      (((r : ℝ) : ℂ) * chordOmega n) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
        ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := by
  sorry
/-- States the paper statement it is bound to from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.binomial_inner_chord_maximal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem binomial_inner_chord_maximal {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ^ n < 1) (hswitch : 1 ≤ r ^ n * (1 + chordCos n ^ n)) :
    ‖(chordPoint n (innerRadius n r) (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = 1 ∧
      (∀ s : ℝ, innerRadius n r < s → s ≤ r →
        1 < ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsD

namespace PalomarCorpus.E1041.PaperStatementsAB
open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex
open Polynomial
open Set
/-- Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.weightedProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def weightedProduct {m : ℕ} (c : Fin m → ℂ) (w : Fin m → ℝ) (z : ℂ) : ℝ :=
  ∏ k, ‖1 - conj (c k) * z‖ ^ w k
/-- Includes the displayed equality classification; proving the inequality alone is not counted as proving this target. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.WeightedFreePoint, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def WeightedFreePoint : Prop :=
  ∀ (m : ℕ) (c : Fin m → ℂ) (w : Fin m → ℝ),
    (∀ j, ‖c j‖ ≤ 1) → (∀ j, 0 < w j) → (∑ j, w j) = 1 →
      (∑ j, w j * weightedProduct c w (c j) ^ 2) ≤ 1 ∧
      ((∑ j, w j * weightedProduct c w (c j) ^ 2) = 1 ↔ ∀ j, c j = 0)
/-- States res:fp-weighted-all-degree from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.paper_weighted_free_point in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_weighted_free_point : WeightedFreePoint := by
  sorry
end PalomarCorpus.E1041.PaperStatementsAB

namespace PalomarCorpus.E1041.PaperStatementsL
open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex
/-- States res:fp-weighted-all-degree from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.geometric_row_mean_closed_disc_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem geometric_row_mean_closed_disc_le {m : ℕ} (hm : 0 < m) (c : Fin m → ℂ)
    (hc : ∀ j, ‖c j‖ ≤ 1) :
    (∑ j, (∏ k, ‖1 - conj (c j) * c k‖) ^ ((m : ℝ)⁻¹)) ≤ (m : ℝ) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsL

namespace PalomarCorpus.E1041.CriticalValueMean
open Finset
open Polynomial Set
open scoped BigOperators
open Polynomial
open scoped ComplexConjugate
open scoped ENNReal
open Polynomial Metric
open Polynomial
open scoped BigOperators
/-- Every zero of the complex polynomial `p` lies in the closed disc of radius `R` about `h`: `p.eval z = 0` implies `‖z - h‖ ≤ R`. -/
noncomputable def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R
/-- The family `c` indexed by `Fin (n - 1)` lists the critical points of `p` with multiplicity: the derivative of `p` equals `C (n : ℂ)` times the product over `j` of `X - C (c j)`. For a monic `p` of degree `n` this says that `c` enumerates the `n - 1` zeros of the derivative, each as often as its multiplicity. -/
noncomputable def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))
/-- Critical-value mean in every degree. Let `n ≥ 2`, let `p` be a monic complex polynomial of degree `n` all of whose zeros lie in the closed disc of radius `R ≥ 0` about a centre `h`, and let `c` enumerate its `n - 1` critical points with multiplicity. Then the sum over `j` of `‖p (c j)‖ ^ (2 / (n - 1))` is at most `(n - 1) R ^ (2 n / (n - 1))`, and the sum over `j` of `‖p (c j)‖ ^ (1 / n)` is at most `(n - 1) R`. The exponents are real powers, the centre `h` is arbitrary, and the degenerate radius `R = 0` is included. -/
theorem paper_critical_value_mean (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ) (h : ℂ) (R : ℝ)
    (hn : 2 ≤ n) (hp : p.Monic) (hdeg : p.natDegree = n) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc p h R) (hc : CriticalEnumeration p c) :
    (∑ j, ‖p.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
        ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
      (∑ j, ‖p.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R := by
  sorry
end PalomarCorpus.E1041.CriticalValueMean

namespace PalomarCorpus.E1041.PaperStatementsF
open Set
open Filter
open MeasureTheory
open scoped Topology
/-- `coth t = cosh t / sinh t`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.coth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def coth (t : ℝ) : ℝ := Real.cosh t / Real.sinh t
/-- The integrand `1 / log (coth t)` of the paper's `Φ`, carrying the paper's continuous limiting value `0` at `t = 0`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def orliczKernel (t : ℝ) : ℝ := 1 / Real.log (coth t)
/-- `Φ(x) = ∫_0^x dt / log (coth t)`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.Phi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def Phi (x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, orliczKernel t
/-- `I_k(r) = ∫_r^1 dq / (q * log ((1 + q ^ (2/k)) / (1 - q ^ (2/k))))`. Local copy of ErdosProblems.Erdos1041.PaperCompleteR21.mergerIntegral, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mergerIntegral (k : ℕ) (r : ℝ) : ℝ :=
  ∫ q in r..(1 : ℝ),
    1 / (q * Real.log ((1 + q ^ ((2 : ℝ) / k)) / (1 - q ^ ((2 : ℝ) / k))))
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.exists_mergerIntegral_lt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_mergerIntegral_lt {k : ℕ} (hk : 1 ≤ k) {c : ℝ} (hc : 0 < c) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ mergerIntegral k r < c * (Real.log (1 / r) / k) := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.mergerIntegral_eq_mul_phi in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mergerIntegral_eq_mul_phi {k : ℕ} (hk : 1 ≤ k) {r : ℝ}
    (hr0 : 0 < r) (hr1 : r ≤ 1) :
    mergerIntegral k r = k * Phi (Real.log (1 / r) / k) := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_continuous in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orliczKernel_continuous : Continuous orliczKernel := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.orliczKernel_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orliczKernel_tendsto_zero : Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.orlicz_currency in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem orlicz_currency :
    (Tendsto orliczKernel (𝓝[≠] (0 : ℝ)) (𝓝 0) ∧ orliczKernel 0 = 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ r : ℝ, 0 < r → r ≤ 1 →
        mergerIntegral k r = k * Phi (Real.log (1 / r) / k)) ∧
      StrictMonoOn Phi (Ioi (0 : ℝ)) ∧
      MonotoneOn Phi (Ioi (0 : ℝ)) ∧
      StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi ∧
      Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      (∀ k : ℕ, 1 ≤ k → ∀ c : ℝ, 0 < c → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
        mergerIntegral k r < c * (Real.log (1 / r) / k)) ∧
      ¬ ∃ c : ℝ, 0 < c ∧ ∀ k : ℕ, 1 ≤ k → ∀ r : ℝ, 0 < r → r < 1 →
        c * (Real.log (1 / r) / k) ≤ mergerIntegral k r := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.phi_div_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem phi_div_tendsto_zero :
    Tendsto (fun x => Phi x / x) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictConvexOn in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem phi_strictConvexOn : StrictConvexOn ℝ (Ioi (0 : ℝ)) Phi := by
  sorry
/-- States res:orlicz-currency from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.phi_strictMonoOn in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem phi_strictMonoOn : StrictMonoOn Phi (Ici (0 : ℝ)) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsF
