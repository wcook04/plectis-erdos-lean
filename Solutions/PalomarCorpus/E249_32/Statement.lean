/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_32

Every non-theorem declaration of `PalomarCorpus/E249_32/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Module
open scoped BigOperators
open ArithmeticFunction

namespace PalomarCorpus.E249_32.Shared
/-- Index type for the canonical duplicate-free family of dyadic totient sections through level `e`: a left index `i ∈ Fin 2` names the zero-residue channel `n ↦ φ(2 ^ i n)`, and a right index `⟨j, r⟩` with `j < e` and `r < 2 ^ j` names the odd residue `2 r + 1` at level `j + 1`, so the type has `2 ^ e + 1` elements. -/
noncomputable abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)
/-- The dyadic section `n ↦ φ(2 ^ j n + r)` of Euler's totient at level `j` and residue `r`, with values in `ℚ` through the cast from `ℕ`. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)
/-- The canonical duplicate-free family of dyadic totient sections through level `e`: a left index `i ∈ Fin 2` gives `n ↦ φ(2 ^ i n)`, and a right index `⟨j, r⟩` gives the odd-residue channel `n ↦ φ(2 ^ (j + 1) n + 2 r + 1)`. -/
noncomputable def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ =>
      totientKernelSeq (j.val + 1) (2 * r.val + 1)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249_32.Shared

namespace PalomarCorpus.E249.CarryRankFrontier
export PalomarCorpus.E249_32.Shared (TotientCanonicalIndex canonicalTotientKernelFamily totientKernelSeq totientTail)
/-- The binary value `∑_{n ≥ 1} c(n) / 2 ^ n` of a natural-number coefficient sequence, written with the summation index shifted so that the term `n = 0` carries `c 1 / 2`. At `c = φ` it is the binary totient series `S`. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The property that `u : ℕ → ℤ` is a tempered integral carry for the coefficient sequence `c` with multiplier `v`: `u (N + 1) = 2 u N - v c (N + 1)` for every `N`, and `u N / 2 ^ N → 0` as `N → ∞`. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Filter.Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N)
      Filter.atTop (nhds 0)
/-- The dyadic section `n ↦ u (2 ^ j n + r)` of a carry sequence `u` at level `j` and residue `r`, with values in `ℚ` through the cast from `ℤ`. -/
noncomputable def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)
/-- Index type for the carry sections through depth `e`: an entry `⟨j, r⟩` with `j < e` and `r < 2 ^ (j + 1)` names the section at level `j + 1` and residue `r`, so every residue is kept at each level. -/
noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))
/-- The family of carry sections indexed by `TotientCarryIndex e`, sending `⟨j, r⟩` to `n ↦ u (2 ^ (j + 1) n + r)`. -/
noncomputable def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val
/-- A finite nonsingularity certificate for a finite family of rational sequences: one evaluation row index `rowIndex i` per index `i`, together with a proof that the square matrix of values `family j (rowIndex i)` has nonzero determinant. Its existence witnesses linear independence of the family. -/
structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) where
  rowIndex : ι → ℕ
  det_ne_zero :
    Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0
/-- The property that every dyadic section of the carry `u` is eventually periodic modulo `v` with the single period `h`: for all `j`, `r` and all `n ≥ N₀`, `u (2 ^ j n + r) ≡ u (2 ^ j (n + h) + r)` modulo `v`. -/
noncomputable def CarrySectionsEventuallyPeriodicMod
    (v h N₀ : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j r n : ℕ, N₀ ≤ n →
    u (2 ^ j * n + r) ≡ u (2 ^ j * (n + h) + r) [ZMOD (v : ℤ)]
end PalomarCorpus.E249.CarryRankFrontier

namespace PalomarCorpus.E249.DyadicTotientKernel
open Module
export PalomarCorpus.E249_32.Shared (TotientCanonicalIndex canonicalTotientKernelFamily totientKernelSeq)
/-- Index type for every dyadic totient section at levels `0` through `e` before any reduction: the pairs `⟨j, r⟩` with `j ≤ e` and `r < 2 ^ j`, so the type has `1 + 2 + ⋯ + 2 ^ e` elements. -/
noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)
/-- The complete unreduced family of dyadic totient sections through level `e`, sending `⟨j, r⟩` to `n ↦ φ(2 ^ j n + r)`. -/
noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val
/-- Index type for the full dyadic kernel of Euler's totient: all pairs `⟨j, r⟩` with `j` a natural number and `r < 2 ^ j`. -/
noncomputable abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)
/-- The full dyadic kernel family of Euler's totient, sending `⟨j, r⟩` to `n ↦ φ(2 ^ j n + r)` at every level `j` and every residue `r < 2 ^ j`. -/
noncomputable def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val
/-- Index type for the odd-core family: two zero-residue channels, together with the `2 ^ j` odd residues at each level `j + 1`. -/
noncomputable abbrev TotientOddCoreIndex := Fin 2 ⊕ Σ j : ℕ, Fin (2 ^ j)
/-- The odd-core family of dyadic totient sections: a left index `i ∈ Fin 2` gives `n ↦ φ(2 ^ i n)`, and a right index `⟨j, r⟩` gives `n ↦ φ(2 ^ (j + 1) n + 2 r + 1)`. -/
noncomputable def oddCoreTotientKernelFamily : TotientOddCoreIndex → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j + 1) (2 * r.val + 1)
end PalomarCorpus.E249.DyadicTotientKernel

namespace PalomarCorpus.E249.FareyWindowExclusion
/-- The explicit denominator bound `79639646646701375323355774875831053`, about `7.96 · 10 ^ 34`, reached by the Farey window computation. -/
def fareyDenBound : ℕ := 79639646646701375323355774875831053
end PalomarCorpus.E249.FareyWindowExclusion

namespace PalomarCorpus.E249.FullDepthRayAmplifier
open scoped BigOperators
export PalomarCorpus.E249_32.Shared (totientTail)
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) -
      (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- The supply of window certificates on multiples of every period: for every `d > 0` and every threshold `c` there are `t > 0`, a basepoint `N ≥ c` and a window length `L` with `certifiedKill (t d) N L`. -/
noncomputable def PeriodMultipleKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L
/-- The full-depth escape statement: for every `d > 0` and every basepoint `N` there is `t > 0` with `certifiedKill (t d) N (t d)`, a certificate whose window length equals its shift. -/
noncomputable def ApFullDepthEscape : Prop :=
  ∀ d : ℕ, 0 < d → ∀ N : ℕ,
    ∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)
/-- The set of multipliers `t` for which the full-depth certificate `certifiedKill (t d) N (t d)` holds at shift step `d` and basepoint `N`. -/
noncomputable def fullDepthKillMultipliers (d N : ℕ) : Set ℕ :=
  {t | certifiedKill (t * d) N (t * d)}
/-- The cofinal form of full-depth supply: for every `d > 0` and every threshold `c` there are `t > 0` and a basepoint `N ≥ c` with `certifiedKill (t d) N (t d)`. -/
noncomputable def CofinalFullDepthKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N (t * d)
end PalomarCorpus.E249.FullDepthRayAmplifier

namespace PalomarCorpus.E249.MobiusMersenneLadderStructure
open scoped BigOperators
open ArithmeticFunction
/-- The atom of index `n` at rung `r` of the Möbius-Mersenne ladder, namely `μ(n + 1) / (2 ^ (n + 1) - 1) ^ r` with `μ` the Möbius function; the index is shifted so that `n = 0` carries the divisor `d = 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The rung `Θ_r = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne ladder, defined as the real sum of the atoms above. The divisor convolution `φ = μ * id` gives `Θ_2 = S - 1/2` for the binary totient series `S = ∑_{n ≥ 1} φ(n) / 2 ^ n`. At `r = 0` the family is not summable and the Lean sum takes its default value `0`; every compared theorem uses the ladder only at `r ≥ 1`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The Möbius-Lambert sum with denominator 2^(rd) − 1 over positive integers d. -/
noncomputable def mobiusMersenneLambertRung (r : ℕ) : ℝ :=
  ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (r * (d : ℕ)) - 1)
end PalomarCorpus.E249.MobiusMersenneLadderStructure
