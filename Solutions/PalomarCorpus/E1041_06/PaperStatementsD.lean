/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCompleteR21.BinomialChords
import ErdosProblems.Erdos1041.PaperCurveAssembly
import Solutions.PalomarCorpus.E1041_06.Statement

open Set
open scoped ENNReal
open scoped NNReal

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsD

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

end PalomarCorpus.E1041.PaperStatementsD
