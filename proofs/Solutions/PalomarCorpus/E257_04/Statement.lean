/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E257_04

Every non-theorem declaration of `PalomarCorpus/E257_04/Challenge.lean`, verbatim and in
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

namespace PalomarCorpus.E257_04.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
end PalomarCorpus.E257_04.Shared

namespace PalomarCorpus.E257.PaperStatementsA
open Filter
open Set
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
end PalomarCorpus.E257.PaperStatementsA

namespace PalomarCorpus.E257.PaperStatementsAA
/-- The finite Mersenne sum associated with a skip set. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.skipSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def skipSum (S : Finset ℕ) : ℚ := ∑ d ∈ S, 1 / ((2 : ℚ) ^ d - 1)
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAE
open Filter
open Set
/-- The radius of the balanced-pulse family at location `m`. Local copy of Erdos249257.balancedPulseRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2
/-- A two-site pulse whose mass can be moved from position `m` to `m+1` without changing its binary-series value. Local copy of Erdos249257.balancedPulseCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0
end PalomarCorpus.E257.PaperStatementsAE

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_04.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- A finite half-gap witness in the cut-locator coordinates. Local copy of Erdos249257.ExistsFatalHalfGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExistsFatalHalfGap : Prop :=
  ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
      < 1 / 2 ∧
    (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
      + mersenneWeight (d + 1)
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
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStructuresS
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_04.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- **Packet §4.** A finite support word certified to straddle the target at depth `d`: the coded value is at most `t` and the value plus the complete unresolved tail mass still reaches `t`. This is deliberately *weaker* than the `HalfPrefixForcingChain.interval_trapped` containment condition: overlap of the correction image with the cylinder, not containment inside it. Local copy of Erdos249257.IsStraddlePrefix, restated so the compared statements elaborate against Mathlib alone. -/
structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
end PalomarCorpus.E257.PaperStructuresS
