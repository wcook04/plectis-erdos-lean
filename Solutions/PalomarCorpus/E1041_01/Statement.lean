/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E1041_01

Every non-theorem declaration of `PalomarCorpus/E1041_01/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped ENNReal
open Polynomial
open Metric
open MeasureTheory
open scoped ComplexConjugate
open Set
open scoped NNReal

namespace PalomarCorpus.E1041_01.Shared
/-- Local definition s, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def s : ℚ := 1 / 10 ^ 6
/-- Local definition t, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def t : ℚ := 417 / 40
/-- Local definition A, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def A : ℚ := -5 + 12 * t - 3 * t ^ 2
/-- Local definition B, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def B : ℚ := -4 + 4 * t + 6 * t ^ 2
/-- Local definition Cconst, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def Cconst : ℚ := t * (-8 + 15 * t - 2 * t ^ 2)
/-- Local definition a, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def a : ℂ := (A : ℂ) - (s : ℂ) * Complex.I
/-- Local definition b, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def b : ℂ := Complex.I * (B : ℂ) + (9 / 5 : ℚ) * (s : ℂ)
/-- Local definition c, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def c : ℂ := -(Cconst : ℂ) - (162 / 25 : ℚ) * (s : ℂ) * Complex.I
noncomputable def ε : ℚ := s ^ 2
noncomputable def ρ : ℚ := 1 - s ^ 16
/-- Local definition f, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def f : Polynomial ℂ :=
  Polynomial.X ^ 7
    + Polynomial.C (-(ρ : ℂ) * (ε : ℂ) ^ 6 * conj c) * Polynomial.X ^ 6
    + Polynomial.C (-(ρ : ℂ) ^ 2 * (ε : ℂ) ^ 5 * conj b) * Polynomial.X ^ 5
    + Polynomial.C (-(ρ : ℂ) ^ 3 * (ε : ℂ) ^ 4 * conj a) * Polynomial.X ^ 4
    + Polynomial.C ((ρ : ℂ) ^ 4 * (ε : ℂ) ^ 4 * a) * Polynomial.X ^ 3
    + Polynomial.C ((ρ : ℂ) ^ 5 * (ε : ℂ) ^ 5 * b) * Polynomial.X ^ 2
    + Polynomial.C ((ρ : ℂ) ^ 6 * (ε : ℂ) ^ 6 * c) * Polynomial.X
    + Polynomial.C (-(ρ : ℂ) ^ 7)
/-- A public function spelling exactly the trinomial in both papers. Local copy of ErdosProblems.Erdos1041.PaperTrinomial.polynomialValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def polynomialValue (n m : ℕ) (a b z : ℂ) : ℂ := z ^ n + a * z ^ m + b
end PalomarCorpus.E1041_01.Shared

namespace PalomarCorpus.E1041.PaperStatementsA
open scoped ENNReal
open Polynomial
open Metric
end PalomarCorpus.E1041.PaperStatementsA

namespace PalomarCorpus.E1041.PaperStatementsAE
open scoped ENNReal
open MeasureTheory
open Polynomial
open Metric
open scoped ComplexConjugate
export PalomarCorpus.E1041_01.Shared (s)
/-- Local definition fcLength, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def fcLength (s : Set ℂ) : ℝ≥0∞ := μH[1] s
end PalomarCorpus.E1041.PaperStatementsAE

namespace PalomarCorpus.E1041.PaperStructuresAF
open scoped ComplexConjugate
open scoped ENNReal
export PalomarCorpus.E1041_01.Shared (A B Cconst a b c f s t)
/-- Local definition pathLength, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def pathLength (γ : ℝ → ℂ) : ENNReal := eVariationOn γ (Set.Icc 0 1)
end PalomarCorpus.E1041.PaperStructuresAF

namespace PalomarCorpus.E1041.PaperStructuresAG
open scoped ENNReal
open MeasureTheory
open Polynomial
open Metric
open scoped ComplexConjugate
export PalomarCorpus.E1041_01.Shared (A B Cconst a b c f s t)
/-- Local definition Omega, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def Omega (p : Polynomial ℂ) : Set ℂ := {z : ℂ | ‖p.eval z‖ < 1}
end PalomarCorpus.E1041.PaperStructuresAG

namespace PalomarCorpus.E1041.PaperStatementsAA
open Set
open scoped NNReal
open scoped ENNReal
export PalomarCorpus.E1041_01.Shared (polynomialValue)
/-- A continuous broken line `a → h → b`, with no division by a segment length. Local copy of ErdosProblems.Erdos1041.PaperCurve.hub, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hub (a h b : ℂ) (t : ℝ) : ℂ :=
  h + ((max (1 - t) 0 : ℝ) : ℂ) * (a - h) + ((max (t - 1) 0 : ℝ) : ℂ) * (b - h)
end PalomarCorpus.E1041.PaperStatementsAA

namespace PalomarCorpus.E1041.PaperStatementsH
open Set
export PalomarCorpus.E1041_01.Shared (polynomialValue)
end PalomarCorpus.E1041.PaperStatementsH
