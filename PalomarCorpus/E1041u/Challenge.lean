/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #1041, band u

Erdős problem #1041 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E1041` under the Challenge size ceiling; it does not replace it.
-/

open Polynomial
open Set
open scoped BigOperators
open scoped NNReal
open scoped ENNReal

namespace PalomarCorpus.E1041.PaperStatementsU
open Polynomial
open Set
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
/-- The geometric conclusion used by the paper: a continuous rectifiable curve with specified endpoints, containment at every parameter, and a strict variation bound. Local copy of ErdosProblems.Erdos1041.PaperCurve.ConnectedBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ConnectedBelow (f : ℂ → ℂ) (R L : ℝ) (a b : ℂ) : Prop :=
  ∃ γ : ℝ → ℂ, ContinuousOn γ (Icc (0 : ℝ) 2) ∧
    γ 0 = a ∧ γ 2 = b ∧
    (∀ t ∈ Icc (0 : ℝ) 2, ‖f (γ t)‖ < R) ∧
    BoundedVariationOn γ (Icc (0 : ℝ) 2) ∧
    eVariationOn γ (Icc (0 : ℝ) 2) < ENNReal.ofReal L
/-- A continuous broken line `a → h → b`, with no division by a segment length. Local copy of ErdosProblems.Erdos1041.PaperCurve.hub, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hub (a h b : ℂ) (t : ℝ) : ℂ :=
  h + ((max (1 - t) 0 : ℝ) : ℂ) * (a - h) + ((max (t - 1) 0 : ℝ) : ℂ) * (b - h)
/-- A specified two-segment connector, rather than merely existence of some rectifiable curve. The public `hub` fixes its image and parametrisation. Local copy of ErdosProblems.Erdos1041.PaperCurve.HubBelow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def HubBelow (f : ℂ → ℂ) (R L : ℝ) (a h b : ℂ) : Prop :=
  (∀ t ∈ Icc (0 : ℝ) 2, ‖f (hub a h b t)‖ < R) ∧
    eVariationOn (hub a h b) (Icc (0 : ℝ) 2) < ENNReal.ofReal L
/-- Occurrences, not necessarily different locations. Local copy of ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.rootProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rootProduct (w : Fin 5 → ℂ) (z : ℂ) : ℂ :=
  (z - w 0) * (z - w 1) * (z - w 2) * (z - w 3) * (z - w 4)
/-- The precise primitive quintic function. Local copy of ErdosProblems.Erdos1041.PaperPrimitivePath.value, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def value (a b c z : ℂ) : ℂ := z ^ 5 + a * z ^ 4 + b * z + c
/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.primitive_quintic_two_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
            eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0)) := by
  sorry
/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.primitive_quintic_two_tail_of_polynomial in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
              eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0)) := by
  sorry
/-- States res:primitive-quintic from the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.complete_primitive_quintic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
          eVariationOn (fun _ : ℝ => w i) (Icc (0 : ℝ) 2) = 0) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsU
