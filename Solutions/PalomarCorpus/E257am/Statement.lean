/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257am

Every non-theorem declaration of `PalomarCorpus/E257am/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- A finite half-gap witness in the cut-locator coordinates. Local copy of Erdos249257.ExistsFatalHalfGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExistsFatalHalfGap : Prop :=
  ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
      < 1 / 2 ∧
    (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
      + mersenneWeight (d + 1)
/-- The Erdős–Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- One term of the binary coding of the achievement set. Local copy of Erdos249257.mersenneDigitTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)
/-- The positive gap between one Mersenne weight and the tail after it. Local copy of Erdos249257.mersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n
/-- The support value coded by a binary sequence. Local copy of Erdos249257.positiveMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b
/-- The common denominator `∏_{k=1}^{N} (2^k - 1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.mersenneDen, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneDen (N : ℕ) : ℕ := ∏ k ∈ Finset.range N, (2 ^ (k + 1) - 1)
/-- `2 * mersenneDen N * mersenneWeight n`, an exact natural number whenever `1 ≤ n ≤ N`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.scaledMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scaledMersenneWeight (N n : ℕ) : ℕ := (2 * mersenneDen N) / (2 ^ n - 1)
/-- The scaled rational upper bound for the tail `mersenneTail (d+1)`: the exact weights of ranks `d+2, …, N` plus the enclosure `mersenneTail N < mersenneWeight N`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.certifiedTailBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedTailBound (d N : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (N - (d + 1)), scaledMersenneWeight N (d + 1 + 1 + j))
    + scaledMersenneWeight N N
/-- The scaled value of the finite word coded by a list of bits: bit `i` of the list selects the Mersenne exponent `i + 1`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.certifiedWordValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedWordValue (L : List Bool) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range L.length,
    bif L.getD i false then scaledMersenneWeight N (i + 1) else 0
/-- The finite certificate: a bit word of length `d`, a cutoff `N ≥ d + 1`, and two exact natural-number inequalities saying that the coded word already overshoots `1/2` after the skip at rank `d + 1`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.FatalHalfGapCertificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FatalHalfGapCertificate (p : List Bool × ℕ) : Prop :=
  p.1.length + 1 ≤ p.2 ∧
    certifiedWordValue p.1 p.2 + certifiedTailBound p.1.length p.2 < mersenneDen p.2 ∧
      mersenneDen p.2 <
        certifiedWordValue p.1 p.2 + scaledMersenneWeight p.2 (p.1.length + 1)
/-- The finite Mersenne word coded by a list of bits. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.certWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certWord (L : List Bool) : Finset ℕ :=
  ((Finset.range L.length).filter fun i => L.getD i false = true).image (· + 1)
/-- Binary digit strings supported on `J`. Local copy of ErdosProblems.Erdos257.SupportedMersenneDigits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}
/-- The ordinary Mersenne digit map restricted to a chosen support. Local copy of ErdosProblems.Erdos257.supportedMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1
/-- The achievement set obtained by allowing digits only on `J`. Local copy of ErdosProblems.Erdos257.supportedMersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)
end PalomarCorpus.E257.PaperStatementsAM
