/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269d

Every non-theorem declaration of `PalomarCorpus/E269d/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open scoped BigOperators

namespace PalomarCorpus.E269.PaperStatementsD
open Finset
open scoped BigOperators
/-- Literal real logarithmic-cell relation from the paper. Local copy of ErdosProblems.Erdos269.PaperCompleteR20.SameThreePrimeRealLogCell, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SameThreePrimeRealLogCell (p q r : ℕ) (x y : ℝ) : Prop :=
  ⌊Real.logb p x⌋₊ = ⌊Real.logb p y⌋₊ ∧
    ⌊Real.logb q x⌋₊ = ⌊Real.logb q y⌋₊ ∧
      ⌊Real.logb r x⌋₊ = ⌊Real.logb r y⌋₊
/-- The `{p,q,r}`-smooth lattice point with exponent vector `(i,j,k)`. Local copy of ErdosProblems.Erdos269.smooth3Val, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k
/-- Exponent triples in the paper's real half-open shell. Local copy of ErdosProblems.Erdos269.PaperCompleteR20.realSmoothExponentShell, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realSmoothExponentShell
    (p q r : ℕ) (lo hi : ℝ) (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((range (hp + 1)).product
      ((range (hq + 1)).product (range (hr + 1)))).filter
    fun e => lo ≤ (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ∧
      (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) < hi
/-- Local copy of ErdosProblems.Erdos269.PaperR10.realPrefixExponents, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realPrefixExponents (p q r : ℕ) (x : ℝ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (⌊Real.logb p x⌋₊ + 1)).product
    ((Finset.range (⌊Real.logb q x⌋₊ + 1)).product
      (Finset.range (⌊Real.logb r x⌋₊ + 1)))).filter
        (fun e => (smooth3Val p q r e.1 e.2.1 e.2.2 : ℝ) ≤ x)
/-- Local copy of ErdosProblems.Erdos269.PaperR10.realPrefixLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realPrefixLcm (p q r : ℕ) (x : ℝ) : ℕ :=
  (realPrefixExponents p q r x).lcm
    (fun e => smooth3Val p q r e.1 e.2.1 e.2.2)
/-- Local copy of ErdosProblems.Erdos269.PaperR10.realThreePrimeHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realThreePrimeHeight (p q r : ℕ) (x : ℝ) : ℕ :=
  p ^ ⌊Real.logb p x⌋₊ * q ^ ⌊Real.logb q x⌋₊ * r ^ ⌊Real.logb r x⌋₊
/-- The product of the largest pure `p`-, `q`-, and `r`-powers not exceeding `x`. For a `{p,q,r}`-smooth `x`, this is the running LCM of the smooth prefix. Local copy of ErdosProblems.Erdos269.threePrimeHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
/-- The exact rational lattice kernel attached to the running-LCM height. Local copy of ErdosProblems.Erdos269.threePrimeKernelQ, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹
end PalomarCorpus.E269.PaperStatementsD
