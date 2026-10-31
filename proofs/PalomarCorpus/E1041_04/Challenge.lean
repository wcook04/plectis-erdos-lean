/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1041, record sections 7 to 10: collinear roots and two sparse polynomial families; further families and counterexamples to proposed proof steps; the Newton value equation

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1041, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. A degree-seven counterexample due to ani,
formalised in this corpus, refutes the total-variation formulation of Erdős problem
#1041; the theorems in this entry keep their stated hypotheses.
-/

open Polynomial
open Set
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
open scoped ComplexConjugate
open Real
open Filter
open Metric
open Bornology
open scoped Topology
open AffineSubspace

namespace PalomarCorpus.E1041_04.Shared
/-- The family `c` indexed by `Fin (n - 1)` lists the critical points of `p` with multiplicity: the derivative of `p` equals `C (n : ℂ)` times the product over `j` of `X - C (c j)`. For a monic `p` of degree `n` this says that `c` enumerates the `n - 1` zeros of the derivative, each as often as its multiplicity. -/
noncomputable def CriticalEnumeration {n : ℕ} (p : ℂ[X]) (c : Fin (n - 1) → ℂ) : Prop :=
  p.derivative = C (n : ℂ) * ∏ j, (X - C (c j))
/-- Every zero of the complex polynomial `p` lies in the closed disc of radius `R` about `h`: `p.eval z = 0` implies `‖z - h‖ ≤ R`. -/
noncomputable def RootsInClosedDisc (p : ℂ[X]) (h : ℂ) (R : ℝ) : Prop :=
  ∀ z : ℂ, p.eval z = 0 → ‖z - h‖ ≤ R
/-- Two complex values lie on the same oriented ray from the origin. Local copy of ErdosProblems.Erdos1041.SamePositiveRay, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SamePositiveRay (a b : ℂ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ b = (r : ℂ) * a
/-- Occurrences, not necessarily different locations. Local copy of ErdosProblems.Erdos1041.PaperPrimitiveCompletionR10.rootProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rootProduct (w : Fin 5 → ℂ) (z : ℂ) : ℂ :=
  (z - w 0) * (z - w 1) * (z - w 2) * (z - w 3) * (z - w 4)
/-- The precise primitive quintic function. Local copy of ErdosProblems.Erdos1041.PaperPrimitivePath.value, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def value (a b c z : ℂ) : ℂ := z ^ 5 + a * z ^ 4 + b * z + c
end PalomarCorpus.E1041_04.Shared

namespace PalomarCorpus.E1041.PaperStatementsM
/-- States prop:primitive-quintic-two-tail-energy-selector from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.primitiveInterior_exists_two_tailEnergy_lt_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem primitiveInterior_exists_two_tailEnergy_lt_one
    {r : ℝ}
    {x0 x1 x2 x3 x4 s0 s1 s2 s3 s4 : ℝ}
    (hr : 0 < r) (hr2 : r < 2)
    (hs0 : 0 ≤ s0) (hs0one : s0 ≤ 1) (hx0s : x0 ^ 2 ≤ s0)
    (hs1 : 0 ≤ s1) (hs1one : s1 ≤ 1) (hx1s : x1 ^ 2 ≤ s1)
    (hs2 : 0 ≤ s2) (hs2one : s2 ≤ 1) (hx2s : x2 ^ 2 ≤ s2)
    (hs3 : 0 ≤ s3) (hs3one : s3 ≤ 1) (hx3s : x3 ^ 2 ≤ s3)
    (hs4 : 0 ≤ s4) (hs4one : s4 ≤ 1) (hx4s : x4 ^ 2 ≤ s4)
    (hm1 : x0 + x1 + x2 + x3 + x4 = -r)
    (hm2 : (2 * x0 ^ 2 - s0) + (2 * x1 ^ 2 - s1) +
        (2 * x2 ^ 2 - s2) + (2 * x3 ^ 2 - s3) +
        (2 * x4 ^ 2 - s4) = r ^ 2)
    (hm3 : (4 * x0 ^ 3 - 3 * s0 * x0) +
        (4 * x1 ^ 3 - 3 * s1 * x1) +
        (4 * x2 ^ 3 - 3 * s2 * x2) +
        (4 * x3 ^ 3 - 3 * s3 * x3) +
        (4 * x4 ^ 3 - 3 * s4 * x4) = -r ^ 3) :
    (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s0 ^ 4 * (s0 + r ^ 2 + 2 * r * x0) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s1 ^ 4 * (s1 + r ^ 2 + 2 * r * x1) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1) ∨
      (s2 ^ 4 * (s2 + r ^ 2 + 2 * r * x2) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) ∨
      (s3 ^ 4 * (s3 + r ^ 2 + 2 * r * x3) < 1 ∧
        s4 ^ 4 * (s4 + r ^ 2 + 2 * r * x4) < 1) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsM

namespace PalomarCorpus.E1041.PaperStatementsU
open Polynomial
open Set
open scoped BigOperators
open scoped NNReal
open scoped ENNReal
export PalomarCorpus.E1041_04.Shared (rootProduct value)
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
end PalomarCorpus.E1041.PaperStatementsU

namespace PalomarCorpus.E1041.PaperStatementsV
open Polynomial
open Set
open scoped BigOperators
export PalomarCorpus.E1041_04.Shared (rootProduct value)
/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.tail_le_one_and_eq_iff_of_leading_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_le_one_and_eq_iff_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (hw : ∀ i, ‖w i‖ ≤ 1)
    (i : Fin 5) :
    ‖b * w i + c‖ ≤ 1 ∧ (‖b * w i + c‖ = 1 ↔ ‖w i‖ = 1) := by
  sorry
/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.tail_norm_of_leading_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tail_norm_of_leading_zero {b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value 0 b c z = rootProduct w z) (i : Fin 5) :
    ‖b * w i + c‖ = ‖w i‖ ^ 5 := by
  sorry
/-- States thm:primitive-quintic-two-tail from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR21.two_tails_closedDisc_of_ne_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem two_tails_closedDisc_of_ne_zero {a b c : ℂ} (w : Fin 5 → ℂ)
    (hf : ∀ z, value a b c z = rootProduct w z)
    (hw : ∀ i, ‖w i‖ ≤ 1) (ha : a ≠ 0) :
    ∃ i j : Fin 5, i ≠ j ∧ ‖b * w i + c‖ < 1 ∧ ‖b * w j + c‖ < 1 := by
  sorry
end PalomarCorpus.E1041.PaperStatementsV

namespace PalomarCorpus.E1041.PaperStatementsJ
open scoped ComplexConjugate
/-- States lem:cubic-safe-root-spoke from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.cubic_has_safe_root_spoke in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cubic_has_safe_root_spoke {r s v : ℂ}
    (hr : ‖r‖ < 1) (hs : ‖s‖ < 1) (hv : ‖v‖ < 1) :
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * r - r) * ((t : ℂ) * r - s) * ((t : ℂ) * r - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * s - s) * ((t : ℂ) * s - r) * ((t : ℂ) * s - v)‖ ≤ 1) ∨
    (∀ t : ℝ, 0 ≤ t → t ≤ 1 →
      ‖((t : ℂ) * v - v) * ((t : ℂ) * v - r) * ((t : ℂ) * v - s)‖ ≤ 1) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsJ

namespace PalomarCorpus.E1041.PaperStatementsO
open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate
export PalomarCorpus.E1041_04.Shared (CriticalEnumeration RootsInClosedDisc)
/-- States eq:critical-value-power-budget, eq:critical-value-quadratic-budget, res:critical-value-budget from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.critical_value_three_budgets in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem critical_value_three_budgets {n : ℕ} (hn : 2 ≤ n) (f : ℂ[X])
    (hf : f.Monic) (hdeg : f.natDegree = n) (h : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hroots : RootsInClosedDisc f h R) (c : Fin (n - 1) → ℂ)
    (hc : CriticalEnumeration f c) :
    (∑ j, ‖f.eval (c j)‖ ^ (2 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ j, ‖f.eval (c j)‖ ^ (1 / ((n : ℝ) - 1))) ≤
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ j, ‖f.eval (c j)‖ ^ (1 / (n : ℝ))) ≤ ((n : ℝ) - 1) * R := by
  sorry
end PalomarCorpus.E1041.PaperStatementsO

namespace PalomarCorpus.E1041.PaperStatementsP
open scoped BigOperators
open Polynomial
open Set
open scoped ComplexConjugate
open Real
export PalomarCorpus.E1041_04.Shared (CriticalEnumeration RootsInClosedDisc)
/-- Local copy of ErdosProblems.Erdos1041.radialEqualityPolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def radialEqualityPolynomial (n : ℕ) (h lam : ℂ) : ℂ[X] := (X - C h) ^ n - C lam
/-- States eq:critical-value-power-budget, eq:critical-value-quadratic-budget, res:critical-value-budget from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.critical_value_three_budgets_sharp in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem critical_value_three_budgets_sharp (n : ℕ) (hn : 2 ≤ n) (h lam : ℂ) :
    let R := ‖lam‖ ^ (1 / (n : ℝ))
    let f := radialEqualityPolynomial n h lam
    f.Monic ∧ f.natDegree = n ∧ RootsInClosedDisc f h R ∧
    CriticalEnumeration f (fun _ : Fin (n - 1) => h) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (2 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ (2 * (n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / ((n : ℝ) - 1))) =
      ((n : ℝ) - 1) * R ^ ((n : ℝ) / ((n : ℝ) - 1)) ∧
    (∑ _j : Fin (n - 1), ‖f.eval h‖ ^ (1 / (n : ℝ))) = ((n : ℝ) - 1) * R := by
  sorry
end PalomarCorpus.E1041.PaperStatementsP

namespace PalomarCorpus.E1041.PaperStatementsW
open Polynomial
open Set
open Filter
open Metric
open Bornology
open scoped BigOperators
open scoped ComplexConjugate
open scoped Topology
export PalomarCorpus.E1041_04.Shared (CriticalEnumeration RootsInClosedDisc)
/-- Reflected-derivative bound, with the derivative root multiplicities specified by an exact polynomial factorisation. Local copy of ErdosProblems.Erdos1041.PaperAnalyticTargets.ReflectedCriticalValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ReflectedCriticalValue : Prop :=
  ∀ (n : ℕ) (p : ℂ[X]) (c : Fin (n - 1) → ℂ), 2 ≤ n → p.Monic →
    p.natDegree = n → RootsInClosedDisc p 0 1 → CriticalEnumeration p c →
      ∀ j, ‖p.eval (c j)‖ ≤ ∏ k, ‖1 - conj (c k) * c j‖
/-- States eq:critical-reflected-product, res:reflected-critical-value from the long record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperReflectedCompletion.reflected_critical_value in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem reflected_critical_value : ReflectedCriticalValue := by
  sorry
end PalomarCorpus.E1041.PaperStatementsW

namespace PalomarCorpus.E1041.PaperStatementsQ
open Set
open Metric
open AffineSubspace
open Polynomial
export PalomarCorpus.E1041_04.Shared (SamePositiveRay)
/-- The complex Newton vector associated with a value and its nonzero derivative. Local copy of ErdosProblems.Erdos1041.newtonFlowVector, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def newtonFlowVector (value derivative : ℂ) : ℂ :=
  -value / derivative
/-- States res:ray from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_endpoint_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem newton_real_endpoint_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn (fun t => f (z t)) (Icc a b))
    (hf : ∀ t ∈ Ioo a b, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ Ioo a b,
      HasDerivAt z (newtonFlowVector (f (z t)) (f' (z t))) t)
    (hc : ∀ t ∈ Ioo a b, f' (z t) ≠ 0) :
    f (z b) = (Real.exp (a - b) : ℂ) * f (z a) ∧
      SamePositiveRay (f (z a)) (f (z b)) := by
  sorry
/-- States res:value from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.PaperCompleteR20.newton_real_value_whole in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem newton_real_value_whole
    {f f' : ℂ → ℂ} {z : ℝ → ℂ} {I : Set ℝ} (hI : OrdConnected I)
    (hf : ∀ t ∈ I, HasDerivAt f (f' (z t)) (z t))
    (hz : ∀ t ∈ I,
      HasDerivWithinAt z (newtonFlowVector (f (z t)) (f' (z t))) I t)
    (hc : ∀ t ∈ I, f' (z t) ≠ 0) :
    (∀ t ∈ I, HasDerivWithinAt (fun s => f (z s)) (-f (z t)) I t) ∧
    (∀ t ∈ I, ∀ t₀ ∈ I,
      f (z t) = (Real.exp (-(t - t₀)) : ℂ) * f (z t₀)) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsQ

namespace PalomarCorpus.E1041.PaperStatementsN
open Set
open Metric
open AffineSubspace
open Polynomial
export PalomarCorpus.E1041_04.Shared (SamePositiveRay)
/-- States res:locus from the long record and the short record for Erdős problem #1041. Transported from ErdosProblems.Erdos1041.translated_samePositiveRay_parameterization in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem translated_samePositiveRay_parameterization
    {a b shift : ℂ} (hab : a ≠ b)
    (hray : SamePositiveRay (a + shift) (b + shift)) :
    ∃ r : ℝ, 0 < r ∧ r ≠ 1 ∧
      shift = ((r : ℂ) * a - b) / ((1 - r : ℝ) : ℂ) := by
  sorry
end PalomarCorpus.E1041.PaperStatementsN
