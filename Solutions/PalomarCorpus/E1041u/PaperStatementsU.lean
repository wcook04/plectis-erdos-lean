/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperCompleteR21.PrimitiveQuinticClosedDisc
import ErdosProblems.Erdos1041.PaperCurveAssembly
import ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10
import ErdosProblems.Erdos1041.PaperPrimitivePath
import Solutions.PalomarCorpus.E1041u.Statement

open Polynomial
open Set
open scoped BigOperators
open scoped NNReal
open scoped ENNReal

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsU

theorem primitive_quintic_two_tail (a b c : ℂ) (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z) :
    ((∀ i, ‖w i‖ ≤ 1) →
        (∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ ≤ 1 ∧ ‖b * w j + c‖ ≤ 1) ∧
        (a ≠ 0 → ∃ i j : Fin 5, i ≠ j ∧
          ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1) ∧
        (a = 0 → ∀ i : Fin 5,
          ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1))) ∧
      ((∀ i, ‖w i‖ < 1) →
        ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 ∧
          ConnectedBelow (value a b c) 1 2 (w i) (w j) ∧
          (w i ≠ w j → HubBelow (value a b c) 1 2 (w i) 0 (w j)) ∧
          (w i = w j →
            (∀ t : ℝ, ‖value a b c ((fun _ : ℝ => w i) t)‖ < 1) ∧
            eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0)) := @ErdosProblems.Erdos1041.PaperCompleteR21.primitive_quintic_two_tail a b c w hf

theorem primitive_quintic_two_tail_of_polynomial (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = 5) (a b c : ℂ)
    (hvalue : ∀ z, p.eval z = value a b c z) :
    ∃ w : Fin 5 → ℂ, (∀ z, p.eval z = rootProduct w z) ∧
      ((∀ i, ‖w i‖ ≤ 1) →
          (∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ ≤ 1 ∧ ‖b * w j + c‖ ≤ 1) ∧
          (a ≠ 0 → ∃ i j : Fin 5, i ≠ j ∧
            ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1) ∧
          (a = 0 → ∀ i : Fin 5,
            ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1))) ∧
        ((∀ i, ‖w i‖ < 1) →
          ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 ∧
            ConnectedBelow (value a b c) 1 2 (w i) (w j) ∧
            (w i ≠ w j → HubBelow (value a b c) 1 2 (w i) 0 (w j)) ∧
            (w i = w j →
              (∀ t : ℝ, ‖value a b c ((fun _ : ℝ => w i) t)‖ < 1) ∧
              eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0)) := @ErdosProblems.Erdos1041.PaperCompleteR21.primitive_quintic_two_tail_of_polynomial p hp hd a b c hvalue

theorem complete_primitive_quintic (p : ℂ[X]) (hp : p.Monic)
    (hd : p.natDegree = 5) (a b c : ℂ)
    (hvalue : ∀ z, p.eval z = value a b c z)
    (hdisk : ∀ z, p.eval z = 0 → ‖z‖ < 1) :
    ∃ w : Fin 5 → ℂ, (∀ z, p.eval z = rootProduct w z) ∧
      ∃ i j : Fin 5, i ≠ j ∧ ‖b*w i+c‖ < 1 ∧ ‖b*w j+c‖ < 1 ∧
        ConnectedBelow p.eval 1 2 (w i) (w j) ∧
        (w i ≠ w j → HubBelow p.eval 1 2 (w i) 0 (w j)) ∧
        (w i = w j →
          (∀ t : ℝ, ‖p.eval ((fun _ : ℝ => w i) t)‖ < 1) ∧
          eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0) := @ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.complete_primitive_quintic p hp hd a b c hvalue hdisk

end PalomarCorpus.E1041.PaperStatementsU
