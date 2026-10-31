/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041_06

Every non-theorem declaration of `PalomarCorpus/E1041_06/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E1041.PaperStatementsAB

namespace PalomarCorpus.E1041.PaperStatementsL
open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex
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
end PalomarCorpus.E1041.PaperStatementsF
