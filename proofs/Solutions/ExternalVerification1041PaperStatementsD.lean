/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChords
import ErdosProblems.Erdos1041.PaperCurveAssembly

/-!
# Independent restatements for Erdős problem #1041

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChords`,
`ErdosProblems.Erdos1041.PaperCurveAssembly`.
-/

open Set
open scoped ENNReal
open scoped NNReal

namespace Erdos249257.ExternalVerification1041PaperStatementsD

noncomputable def angle (n : ℕ) : ℝ := Real.pi / (n : ℝ)

noncomputable def chordCos (n : ℕ) : ℝ := Real.cos (angle n)

noncomputable def chordEps (n : ℕ) (r : ℝ) : ℝ := (1 - r ^ n) ^ ((n : ℝ)⁻¹)

noncomputable def halfRoot (n : ℕ) : ℂ := Complex.exp ((angle n : ℂ) * Complex.I)

noncomputable def chordOmega (n : ℕ) : ℂ := halfRoot n ^ 2

noncomputable def chordPoint (n : ℕ) (s u : ℝ) : ℂ :=
  (s : ℂ) * (((1 - u : ℝ) : ℂ) + ((u : ℝ) : ℂ) * chordOmega n)

noncomputable def chordThreshold (n : ℕ) : ℝ := (1 + chordCos n ^ n) ^ (-((n : ℝ)⁻¹))

noncomputable def innerRadius (n : ℕ) (r : ℝ) : ℝ := chordEps n r / chordCos n

noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L

theorem binomial_chord_decisive_step {n : ℕ} (hn : 2 ≤ n) {θ : ℝ}
    (hθ : (n : ℝ) * |θ| ≤ Real.pi) :
    1 + Real.cos ((n : ℝ) * θ) ≤ 2 * Real.cos θ ^ n := by
  apply ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chord_decisive_step <;> assumption

theorem binomial_chord_maximum {n : ℕ} (hn : 2 ≤ n) {s r : ℝ} (hs : 0 < s) (hsr : s ≤ r) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n s u) ^ n - ((r : ℝ) : ℂ) ^ n‖ ≤ r ^ n + (s * chordCos n) ^ n) ∧
      ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = r ^ n + (s * chordCos n) ^ n := @ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chord_maximum n hn s r hs hsr

theorem binomial_chords_above_threshold {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hge : chordThreshold n ≤ r) {lam : ℝ} (hl0 : 0 < lam) (hl1 : lam < 1) :
    ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := @ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_above_threshold n hn r hr0 hr1 hge lam hl0 hl1

theorem binomial_chords_at_threshold {n : ℕ} (hn : 2 ≤ n) :
    (∀ u : ℝ, 0 ≤ u → u ≤ 1 →
        ‖(chordPoint n (chordThreshold n) u) ^ n
          - ((chordThreshold n : ℝ) : ℂ) ^ n‖ ≤ 1) ∧
      ‖(chordPoint n (chordThreshold n) (1 / 2)) ^ n
        - ((chordThreshold n : ℝ) : ℂ) ^ n‖ = 1 := @ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_at_threshold n hn

theorem binomial_chords_below_threshold {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r < 1) (hlt : r < chordThreshold n) :
    ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
      ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := @ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_below_threshold n hn r hr0 hr1 hlt

theorem binomial_chords_path {n : ℕ} (hn : 2 ≤ n) {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ((r : ℝ) : ℂ) ≠ ((r : ℝ) : ℂ) * chordOmega n ∧
      (((r : ℝ) : ℂ)) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      (((r : ℝ) : ℂ) * chordOmega n) ^ n - ((r : ℝ) : ℂ) ^ n = 0 ∧
      ConnectedBelow (fun z => z ^ n - ((r : ℝ) : ℂ) ^ n) 1 2
        ((r : ℝ) : ℂ) (((r : ℝ) : ℂ) * chordOmega n) := @ErdosProblems.Erdos1041.PaperCompleteR21.binomial_chords_path n hn r hr0 hr1

theorem binomial_inner_chord_maximal {n : ℕ} (hn : 3 ≤ n) {r : ℝ} (hr0 : 0 < r)
    (hr1 : r ^ n < 1) (hswitch : 1 ≤ r ^ n * (1 + chordCos n ^ n)) :
    ‖(chordPoint n (innerRadius n r) (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖ = 1 ∧
      (∀ s : ℝ, innerRadius n r < s → s ≤ r →
        1 < ‖(chordPoint n s (1 / 2)) ^ n - ((r : ℝ) : ℂ) ^ n‖) := @ErdosProblems.Erdos1041.PaperCompleteR21.binomial_inner_chord_maximal n hn r hr0 hr1 hswitch

end Erdos249257.ExternalVerification1041PaperStatementsD
