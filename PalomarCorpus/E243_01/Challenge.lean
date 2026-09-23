/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #243, record sections 2 to 4: irrationality at the cubic rate; integer numerators, denominators and errors

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #243, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #243 remains open, and no theorem in
this entry decides it.
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
/-- States long243:eq:cubicorbit, long243:res:cubicexclusion from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.cubic_exclusion_unconditional in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cubic_exclusion_unconditional
    (a C D : ℕ → ℤ) (ha : ∀ n, 0 < a n) (hC : ∀ n, 0 < C n) (hD : ∀ n, 0 < D n)
    (hCrec : ∀ n, C (n + 1) = a n * C n - D n)
    (hDrec : ∀ n, D (n + 1) = a n * D n)
    (A B : ℚ) (hA : 0 < A) :
    (∃ dens : ℝ, 0 < dens ∧ ∃ N : ℕ, ∀ X : ℕ, N ≤ X →
        dens * (X : ℝ) ≤ (exceptionCount
          {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}
          (X + 1) : ℝ)) ∧
      ¬ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℚ) = A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B := by
  sorry
/-- States long243:res:cubicrate, res:cubicrate from the long record and the short record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.cubic_rate_irrationality_unconditional in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cubic_rate_irrationality_unconditional
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (hrate : Filter.Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      ((a n : ℝ) ^ 2 / (a (n + 1) : ℝ) - (1 + 3 / (n : ℝ))))
      Filter.atTop (nhds 0))
    (Sv : ℝ) (hS : HasSum (fun n : ℕ => 1 / (a n : ℝ)) Sv) :
    Irrational Sv := by
  sorry
/-- States long243:res:squarespec from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.squareSpecialisation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem squareSpecialisation : SquareSpecialisation := by
  sorry
/-- States long243:res:transportsquare from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.transport_square_unconditional in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem transport_square_unconditional
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (L₀ : Type) [Field L₀] [Algebra ℚ L₀] (α : L₀)
    (hroot : α ^ 3 = α - algebraMap ℚ L₀ (6 * (c : ℚ) / (m : ℚ))) :
    ∃ β ∈ IntermediateField.adjoin ℚ ({α} : Set L₀),
      β ≠ 0 ∧ β ^ 2 = α ^ 2 - 1 := by
  sorry
end PalomarCorpus.E243.PaperStructuresAC

namespace PalomarCorpus.E243.CompletePaperRecords
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E243_01.Shared (LowerDensityAtLeast exceptionCount exceptionFinset)
/-- If each sufficiently late index in one residue class modulo s has a translate in E among L fixed offsets, E has lower density at least 1/(Ls). -/
theorem fixed_offsets_periodic_lowerDensity (E : Set ℕ) (s L T r : ℕ)
    (hs : 0 < s) (hL : 0 < L) (hr : r < s) (offset : Fin L → ℕ)
    (hhit : ∀ n : ℕ, T ≤ n → n % s = r →
      ∃ i : Fin L, n + offset i ∈ E) :
    LowerDensityAtLeast E (1 / ((L : ℝ) * (s : ℝ))) := by
  sorry
end PalomarCorpus.E243.CompletePaperRecords

namespace PalomarCorpus.E243.PaperStatementsA
export PalomarCorpus.E243_01.Shared (ZeroLowerDensity exceptionCount exceptionFinset risingBinomial)
/-- The literal unshifted polynomial printed as Q_{m,c} in the paper. Local copy of ErdosProblems.Erdos243.PaperCompleteR11.rationalBinomialCubic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rationalBinomialCubic (m c : ℚ) : Polynomial ℚ :=
  Polynomial.C (m / 6) * Polynomial.X * (Polynomial.X + 1) *
    (Polynomial.X + 2) + Polynomial.C c
/-- Centering at the Sylvester tail: `Eₙ = Dₙ - (aₙ - 1) Cₙ`. Local copy of ErdosProblems.Erdos243.centeredState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def centeredState (a D C : ℤ) : ℤ :=
  D - (a - 1) * C
/-- Product-cleared denominator update `Dₙ₊₁ = aₙ Dₙ`. Local copy of ErdosProblems.Erdos243.nextDenState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextDenState (a D : ℤ) : ℤ :=
  a * D
/-- Product-cleared reciprocal-tail update `Cₙ₊₁ = aₙ Cₙ - Dₙ`. Local copy of ErdosProblems.Erdos243.nextTailState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def nextTailState (a D C : ℤ) : ℤ :=
  a * C - D
/-- States long243:res:reduciblecase from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR11.primitive_zero_density_paper_multiplier_lemma in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem primitive_zero_density_paper_multiplier_lemma
    (a u v : ℕ → ℕ) (m c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity {n : ℕ | (u n : ℤ) ≠ m * risingBinomial n + c}) :
    (c = 1 ∨ c = -1) ∧
    (∀ n, T ≤ n → Nat.Coprime (a n) (v n)) ∧
    (∀ i j, T ≤ i → T ≤ j → i ≠ j → Nat.Coprime (a i) (a j)) ∧
    (∀ N, ∃ n, max T N ≤ n ∧ 1 < a n) ∧
    (∀ B N, ∃ p j : ℕ, Nat.Prime p ∧ B < p ∧ max T N ≤ j ∧ p ∣ a j) ∧
    Irreducible (rationalBinomialCubic (m : ℚ) (c : ℚ)) := by
  sorry
/-- States long243:eq:Qmc, long243:eq:primitivetail, long243:res:gcdshape from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.cubic_profile_gcd_stabilisation_and_primitive_shape in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem cubic_profile_gcd_stabilisation_and_primitive_shape
    (a C D : ℕ → ℕ) (A B : ℚ) (hA : 0 < A)
    (hCpos : ∀ n, 0 < C n) (hDpos : ∀ n, 0 < D n)
    (hC : ∀ n, C (n + 1) + D n = a n * C n)
    (hD : ∀ n, D (n + 1) = a n * D n)
    (hzero : ZeroLowerDensity
      {n : ℕ | (C n : ℚ) ≠ A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B}) :
    ∃ M : ℤ, 0 < M ∧ (M : ℚ) = 6 * A ∧
      (∀ n : ℕ, (Nat.gcd (C n) (D n) : ℤ) ∣ M) ∧
      ∃ g N : ℕ, 0 < g ∧
        (∀ n, N ≤ n → Nat.gcd (C n) (D n) = g) ∧
        ∃ m c : ℤ, 0 < m ∧ (c = 1 ∨ c = -1) ∧
          (∀ n : ℕ,
            (A * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + B) / (g : ℚ)
              = (m : ℚ) / 6 * (n : ℚ) * ((n : ℚ) + 1) * ((n : ℚ) + 2) + (c : ℚ)) ∧
          (∀ n, N ≤ n →
            C (n + 1) / g + D n / g = a n * (C n / g) ∧
            D (n + 1) / g = a n * (D n / g) ∧
            Nat.Coprime (C n / g) (D n / g) ∧
            Nat.Coprime (C n / g) (C (n + 1) / g) ∧
            0 < C n / g ∧ 0 < D n / g) := by
  sorry
/-- States long243:res:scale from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.state_scale in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem state_scale (s a D C : ℤ) :
    nextDenState a (s * D) = s * nextDenState a D ∧
    nextTailState a (s * D) (s * C) = s * nextTailState a D C ∧
    centeredState a (s * D) (s * C) = s * centeredState a D C := by
  sorry
/-- States long243:res:update from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.nextTailState_eq_sub_centered in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem nextTailState_eq_sub_centered (a D C : ℤ) :
    nextTailState a D C = C - centeredState a D C := by
  sorry
end PalomarCorpus.E243.PaperStatementsA

namespace PalomarCorpus.E243.PaperStatementsP
open Polynomial
open scoped BigOperators
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR11.cubicScalePolynomial, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicScalePolynomial (η : ℚ) : ℚ[X] := X^3 - X + C η
/-- States long243:res:scaletwelve from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR20.scale_twelve_of_square_in_rootField in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scale_twelve_of_square_in_rootField
    {L : Type*} [Field L] [Algebra ℚ L]
    (m : ℕ) (c : ℤ) (hm : 0 < m) (hc : c = 1 ∨ c = -1)
    (α : L)
    (hirr : Irreducible
      (cubicScalePolynomial (6 * (c : ℚ) / (m : ℚ))))
    (hroot : α ^ 3 = α -
      algebraMap ℚ L (6 * (c : ℚ) / (m : ℚ)))
    (hsquare : ∃ β : L,
      β ∈ IntermediateField.adjoin ℚ ({α} : Set L) ∧
      β ^ 2 = α ^ 2 - 1) :
    m = 12 := by
  sorry
end PalomarCorpus.E243.PaperStatementsP

namespace PalomarCorpus.E243.PaperStructuresAD
export PalomarCorpus.E243_01.Shared (LowerDensityAtLeast exceptionCount exceptionFinset)
/-- Local definition cubicTwelveProfile, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def cubicTwelveProfile (c : ℤ) (n : ℕ) : ℤ :=
  2 * (n : ℤ) * ((n : ℤ) + 1) * ((n : ℤ) + 2) + c
/-- States long243:res:modseven from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR20.minus_one_forbidden_word in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem minus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 1 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile (-1) (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile (-1) n} (1 / 7) := by
  sorry
/-- States long243:res:modseven from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR20.plus_one_forbidden_word in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem plus_one_forbidden_word (a u v : ℕ → ℤ) (T : ℕ)
    (hnum : ∀ j, T ≤ j → u (j + 1) + v j = a j * u j)
    (hden : ∀ j, T ≤ j → v (j + 1) = a j * v j) :
    (∀ n, T ≤ n → (n : ZMod 7) = 0 →
      ∃ j : ℕ, j < 4 ∧ u (n + j) ≠ cubicTwelveProfile 1 (n + j)) ∧
    LowerDensityAtLeast {n : ℕ | u n ≠ cubicTwelveProfile 1 n} (1 / 7) := by
  sorry
end PalomarCorpus.E243.PaperStructuresAD

namespace PalomarCorpus.E243.PaperStatementsG
open Filter
open Finset
/-- The literal error in `C (n+1) / C n = 1 + l/n + ε_n`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.rateError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rateError (l : ℝ) (C : ℕ → ℝ) (n : ℕ) : ℝ := C (n + 1) / C n - (1 + l / (n : ℝ))
/-- `risingPow d x = x (x+1) ⋯ (x + d - 1)`. Local copy of ErdosProblems.Erdos243.PaperCompleteR21.risingPow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingPow (d : ℕ) (x : ℝ) : ℝ := ∏ i ∈ Finset.range d, (x + (i : ℝ))
/-- States long243:eq:regularrate, long243:res:extraction from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem regular_rate_extraction {l : ℝ} (hl : 1 < l) (C : ℕ → ℤ)
    (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ l * rateError l (fun j => (C j : ℝ)) n)
      atTop (nhds 0)) :
    ∃ d : ℕ, 2 ≤ d ∧ l = (d : ℝ) ∧
      ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
        (C n : ℝ) = (A : ℝ) * risingPow d (n : ℝ) + (B : ℝ) := by
  sorry
end PalomarCorpus.E243.PaperStatementsG

namespace PalomarCorpus.E243.PaperStatementsN
open Filter
open Finset
/-- Local copy of ErdosProblems.Erdos243.PaperCompleteR20.cubicRatioError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cubicRatioError (C : ℕ → ℝ) (n : ℕ) : ℝ :=
  C (n + 1) / C n - (1 + 3 / (n : ℝ))
/-- The rising cubic used in the paper. Local copy of ErdosProblems.Erdos243.PaperCompleteR20.risingCubic, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def risingCubic (n : ℕ) : ℝ := (n : ℝ) * (n + 1) * (n + 2)
/-- States long243:eq:regularrate, long243:res:extraction from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR21.regular_rate_extraction_cubic in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem regular_rate_extraction_cubic (C : ℕ → ℤ) (hpos : ∀ n, 0 < C n)
    (hratio : Tendsto (fun n : ℕ => (n : ℝ) ^ 3 *
      cubicRatioError (fun j => (C j : ℝ)) n) atTop (nhds 0)) :
    ∃ A B : ℚ, 0 < A ∧ ∃ N : ℕ, ∀ n, N ≤ n →
      (C n : ℝ) = (A : ℝ) * risingCubic n + (B : ℝ) := by
  sorry
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
/-- States long243:res:tailratio from the long record for Erdős problem #243. Transported from ErdosProblems.Erdos243.PaperCompleteR7.canonical_tail_ratio_quantitative in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_tail_ratio_quantitative
    (a : ℕ → ℕ) (ha : StrictMono a) (hpos : ∀ n, 0 < a n)
    (p : ℤ) (q : ℕ) (hq : 0 < q)
    (hs : HasSum (fun n ↦ 1 / (a n : ℝ)) ((p : ℝ) / (q : ℝ)))
    (hgrowth : Tendsto (fun n ↦ (a (n + 1) : ℝ) / (a n : ℝ) ^ 2)
      atTop (nhds 1)) :
    let C := canonicalNaturalNumerator a p q
    (∃ N, ∀ n, N ≤ n →
      |(C (n + 1) : ℝ) / (C n : ℝ) -
        (a n : ℝ) ^ 2 / (a (n + 1) : ℝ)| ≤ 16 / (a n : ℝ)) ∧
    (∃ c : ℝ, 0 < c ∧ ∃ N, ∀ n, N ≤ n →
      Real.exp (c * (2 : ℝ) ^ n) ≤ (a n : ℝ)) := by
  sorry
end PalomarCorpus.E243.PaperStatementsL
