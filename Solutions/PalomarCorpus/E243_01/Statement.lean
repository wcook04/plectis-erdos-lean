/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E243_01

Every non-theorem declaration of `PalomarCorpus/E243_01/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter Topology
open scoped BigOperators
open Polynomial
open Filter
open Finset

namespace PalomarCorpus.E243_01.Shared
/-- The elements of E strictly below X. -/
noncomputable def exceptionFinset (E : Set ℕ) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range X).filter (fun n ↦ n ∈ E)
/-- The number of elements of E strictly below X. -/
noncomputable def exceptionCount (E : Set ℕ) (X : ℕ) : ℕ :=
  (exceptionFinset E X).card
/-- For every positive ε, the count below X is eventually at least (d − ε)X; this is the stated lower-density bound. -/
noncomputable def LowerDensityAtLeast (E : Set ℕ) (d : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
    (d - ε) * (X : ℝ) ≤ (exceptionCount E X : ℝ)
/-- Arbitrarily late prefixes have arbitrarily small exceptional proportion. The strict inequality automatically excludes the zero-length prefix. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.ZeroLowerDensity, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ZeroLowerDensity (E : Set ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ N : ℕ, ∃ X : ℕ,
    N ≤ X ∧ (exceptionCount E X : ℝ) < ε * (X : ℝ)
/-- Integer-valued binomial basis for a rising cubic. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.risingBinomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingBinomial (n : ℕ) : ℤ := ((n + 2).choose 3 : ℤ)
end PalomarCorpus.E243_01.Shared

namespace PalomarCorpus.E243.PaperStructuresAC
export PalomarCorpus.E243_01.Shared (ZeroLowerDensity exceptionCount exceptionFinset risingBinomial)
/-- Local definition SquareSpecialisation, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def SquareSpecialisation : Prop :=
  ∀ (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀) (f H : Polynomial ℚ),
    Irreducible f → Polynomial.aeval α f = 0 → Polynomial.aeval α H ≠ 0 →
    ∀ (d : ℕ), 0 < d → ∀ G J : Polynomial ℤ,
    G.map (Int.castRingHom ℚ) = Polynomial.C (d : ℚ) * f →
    J.map (Int.castRingHom ℚ) = Polynomial.C ((d : ℚ) ^ 2) * H →
    (∃ N : ℕ, ∀ ℓ : ℕ, ℓ.Prime → N < ℓ → ∀ r : ZMod ℓ,
        (G.map (Int.castRingHom (ZMod ℓ))).eval r = 0 →
        (J.map (Int.castRingHom (ZMod ℓ))).eval r ≠ 0 ∧
          IsSquare ((J.map (Int.castRingHom (ZMod ℓ))).eval r)) →
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = Polynomial.aeval α H
end PalomarCorpus.E243.PaperStructuresAC

namespace PalomarCorpus.E243.CompletePaperRecords
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E243_01.Shared (LowerDensityAtLeast exceptionCount exceptionFinset)
end PalomarCorpus.E243.CompletePaperRecords

namespace PalomarCorpus.E243.PaperStatementsA
export PalomarCorpus.E243_01.Shared (ZeroLowerDensity exceptionCount exceptionFinset risingBinomial)
/-- The literal unshifted polynomial printed as Q_{m,c} in the paper. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.rationalBinomialCubic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalBinomialCubic (m c : ℚ) : Polynomial ℚ :=
  Polynomial.C (m / 6) * Polynomial.X * (Polynomial.X + 1) *
    (Polynomial.X + 2) + Polynomial.C c
end PalomarCorpus.E243.PaperStatementsA

namespace PalomarCorpus.E243.PaperStatementsP
open Polynomial
open scoped BigOperators
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR11.cubicScalePolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicScalePolynomial (η : ℚ) : ℚ[X] := X^3 - X + C η
end PalomarCorpus.E243.PaperStatementsP

namespace PalomarCorpus.E243.PaperStructuresAD
export PalomarCorpus.E243_01.Shared (LowerDensityAtLeast exceptionCount exceptionFinset)
/-- Local definition cubicTwelveProfile, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def cubicTwelveProfile (c : ℤ) (n : ℕ) : ℤ :=
  2 * (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) + c
/-- Local definition instFactPrimeOfNatNat_erdosProblems, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable scoped instance instFactPrimeOfNatNat_erdosProblems : Fact (Nat.Prime 7) := ⟨by decide⟩
end PalomarCorpus.E243.PaperStructuresAD

namespace PalomarCorpus.E243.PaperStatementsG
open Filter
open Finset
/-- The literal error in `C (n+1) / C n = 1 + l/n + ε_n`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.rateError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rateError (l : ℝ) (C : ℕ → ℝ) (n : ℕ) : ℝ := C (n + 1) / C n - (1 + l / (n : ℝ))
/-- `risingPow d x = x (x+1) ⋯ (x + d - 1)`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.risingPow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingPow (d : ℕ) (x : ℝ) : ℝ := ∏ i ∈ Finset.range d, (x + (i : ℝ))
end PalomarCorpus.E243.PaperStatementsG

namespace PalomarCorpus.E243.PaperStatementsN
open Filter
open Finset
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR20.cubicRatioError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicRatioError (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (n + 1) / C n - (1 + 3 / (n : ℝ))
/-- The rising cubic used in the paper. Local copy of ErdosProblems.Erdos243.PaperCompleteR20.risingCubic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingCubic (n : ℕ) : ℝ := (n : ℝ) * (n + 1) * (n + 2)
end PalomarCorpus.E243.PaperStatementsN

namespace PalomarCorpus.E243.PaperStatementsL
open Filter
open scoped BigOperators
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.prefixProduct, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prefixProduct (a : ℕ → ℕ) (n : ℕ) : ℕ :=
  ∏ j ∈ Finset.range n, a j
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.clearedIntegerNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def clearedIntegerNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℤ :=
  p * (prefixProduct a n : ℤ) -
    ∑ j ∈ Finset.range n, (q : ℤ) * (prefixProduct a n / a j : ℕ)
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR7.canonicalNaturalNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalNaturalNumerator (a : ℕ → ℕ) (p : ℤ) (q n : ℕ) : ℕ :=
  (clearedIntegerNumerator a p q n).toNat
end PalomarCorpus.E243.PaperStatementsL
