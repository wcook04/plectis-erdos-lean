/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249

Every non-theorem declaration of `PalomarCorpus/E249/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Module
open ArithmeticFunction

namespace PalomarCorpus.E249.Shared
/-- Index type for the canonical duplicate-free family of dyadic totient sections through level `e`: a left index `i ∈ Fin 2` names the zero-residue channel `n ↦ φ(2 ^ i n)`, and a right index `⟨j, r⟩` with `j < e` and `r < 2 ^ j` names the odd residue `2 r + 1` at level `j + 1`, so the type has `2 ^ e + 1` elements. -/
noncomputable abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)
/-- The atom of index `n` at rung `r` of the Möbius-Mersenne ladder, namely `μ(n + 1) / (2 ^ (n + 1) - 1) ^ r` with `μ` the Möbius function; the index is shifted so that `n = 0` carries the divisor `d = 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The rung `Θ_r = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne ladder, defined as the real sum of the atoms above. The divisor convolution `φ = μ * id` gives `Θ_2 = S - 1/2` for the binary totient series `S = ∑_{n ≥ 1} φ(n) / 2 ^ n`. At `r = 0` the family is not summable and the Lean sum takes its default value `0`; every compared theorem uses the ladder only at `r ≥ 1`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The binary block of `H` consecutive totient values starting at `N + 1`, most significant weight first: `∑_{j < H} φ(N + 1 + j) 2 ^ (H - 1 - j)`, an integer. It equals `2 ^ H R_N - R_{N + H}` for the binary totient tail `R_N`, and is `0` when `H = 0`. -/
noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
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
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) -
      (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The window certificate `K(h, N, L)`: the integer remainder of `windowDiscrepancy h N L` modulo `2 ^ L` lies strictly between `N + h + L + 2` and `2 ^ L - (N + h + L + 2)`. By the displayed error bound some `L` satisfies it exactly when the tail difference `R_{N + h} - R_N` is not an integer. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
end PalomarCorpus.E249.Shared

namespace PalomarCorpus.E249.ActualLcmOrbit
open scoped BigOperators
export PalomarCorpus.E249.Shared (totientTail)
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The integer prefix `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` of the scaled binary totient series, so that `2 ^ N S = Φ_N + R_N`; the term at `n = 0` vanishes because `φ(0) = 0`. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
/-- The height `H_a = lcm(1, 2, ..., 2 ^ a)`, used as both the basepoint and the shift of the power-of-two LCM diagonal. -/
noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)
/-- The LCM diagonal orbit value `R_{2 H_a} - R_{H_a}`, the difference of the binary totient tails at the heights `2 H_a` and `H_a`. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)
/-- The supply statement that the LCM diagonal orbit is nonintegral cofinally often: for every threshold `a₀` there is `a ≥ a₀` whose orbit value lies outside the image of `ℤ` in `ℝ`. -/
noncomputable def PowerTwoActualLcmOrbitNonintegralitySupply : Prop :=
  ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ)
end PalomarCorpus.E249.ActualLcmOrbit

namespace PalomarCorpus.E249.BinaryCyclotomicAnchors
open scoped BigOperators
export PalomarCorpus.E249.Shared (certifiedKill totientTail windowDiscrepancy)
/-- The binary cyclotomic layer `|Φ_n(2)|`, the absolute value of the `n`th cyclotomic polynomial over `ℤ` evaluated at `2`, returned as a natural number through `Int.natAbs`. -/
noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs
/-- The property that a layer function `C` has unbounded prime support on the ray of multiples of `h`: for all bounds `B` and `N₀` there are primes `q ≥ N₀` and `p > B` with `p` dividing `C (h q)`. -/
noncomputable def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (h : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (h * q) ∧ B < p
/-- The anchored certificate supply for a layer function `C`: for every period `h > 0` and every threshold `N₀` there are primes `q` and `p` and a window length `L` with `p` coprime to `h q`, `p` dividing `C (h q)`, `h q` dividing `p - 1`, `N₀ ≤ p - 1`, and the window certificate `certifiedKill (h q) (p - 1) L` holding at the basepoint `p - 1`. -/
noncomputable def CyclotomicAnchoredKillSupply (C : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h →
    ∀ N₀ : ℕ, ∃ q p L : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ C (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 ∧
      certifiedKill (h * q) (p - 1) L
end PalomarCorpus.E249.BinaryCyclotomicAnchors

namespace PalomarCorpus.E249.CanonicalMersenneFrontier
open scoped BigOperators
export PalomarCorpus.E249.Shared (totientBlock)
/-- The shifted totient difference `φ(n + h) - φ(n)`, taken in `ℤ` through the cast from `ℕ`. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ :=
  (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The canonical residue of the negated totient block, `(-totientBlock H N) mod M`, computed with the integer remainder, so for `M > 0` it is the representative in `[0, M)`; at `M = 0` the remainder is the argument itself. -/
noncomputable def fullMersenneBlockResidue (H N M : ℕ) : ℤ :=
  (-totientBlock H N) % (M : ℤ)
/-- The centred gap condition at `(H, N, M)`: writing `B = N + H + 1`, the canonical residue `fullMersenneBlockResidue H N M` lies strictly between `B` and `M - B`, that is, further than `B` from both ends of its residue range. -/
noncomputable def FullMersenneCenteredResidueGap (H N M : ℕ) : Prop :=
  let B : ℤ := N + H + 1
  B < fullMersenneBlockResidue H N M ∧
    fullMersenneBlockResidue H N M < (M : ℤ) - B
/-- The cofinal supply statement: for every basepoint bound `c`, every `v > 0` with `v` odd (written `Nat.Coprime 2 v`) and every threshold `N₀`, there are `H > 0` divisible by `φ(v)`, a basepoint `N ≥ max c N₀` and `M` with `v M = 2 ^ H - 1` such that the centred gap holds at `(H, N, M)`. -/
noncomputable def FullMersenneCenteredResidueGapSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∀ N₀ : ℕ, ∃ H N M : ℕ,
      0 < H ∧ Nat.totient v ∣ H ∧ max c N₀ ≤ N ∧
      v * M = 2 ^ H - 1 ∧ FullMersenneCenteredResidueGap H N M
/-- The canonical basepoint form of the same supply, with the basepoint pinned at `c` instead of allowed to move: for every `c` and every odd `v > 0` there are `H > 0` divisible by `φ(v)` and `M` with `v M = 2 ^ H - 1` such that the centred gap holds at `(H, c, M)`. -/
noncomputable def FullMersenneCanonicalBasepointResidueGapSupply : Prop :=
  ∀ c v : ℕ, 0 < v → Nat.Coprime 2 v →
    ∃ H M : ℕ,
      0 < H ∧ Nat.totient v ∣ H ∧ v * M = 2 ^ H - 1 ∧
      FullMersenneCenteredResidueGap H c M
end PalomarCorpus.E249.CanonicalMersenneFrontier

namespace PalomarCorpus.E249.CarryRankFrontier
export PalomarCorpus.E249.Shared (TotientCanonicalIndex canonicalTotientKernelFamily totientKernelSeq totientTail)
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
export PalomarCorpus.E249.Shared (TotientCanonicalIndex canonicalTotientKernelFamily totientKernelSeq)
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
export PalomarCorpus.E249.Shared (certifiedKill totientTail windowDiscrepancy)
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
export PalomarCorpus.E249.Shared (mobiusMersenneTerm mobiusMersenneTheta)
end PalomarCorpus.E249.MobiusMersenneLadderStructure

namespace PalomarCorpus.E249.PrefixTwoAdicExclusion
/-- The integer prefix `P_n = ∑_{i < n} 2 ^ (n - 1 - i) φ(i + 1)` of `2 ^ n S`, written over the first `n` positive arguments; `P_0 = 0`. -/
noncomputable def totientPrefix (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * Nat.totient (i + 1)
/-- The local tail `R_n = 2 ^ n S - P_n` of an arbitrary real number `S` against the totient prefix. It is stated for a general `S` so that the exclusion theorems below can carry a rational form for `S` as an explicit hypothesis. -/
noncomputable def prefixTail (S : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * S - (totientPrefix n : ℝ)
end PalomarCorpus.E249.PrefixTwoAdicExclusion

namespace PalomarCorpus.E249.RankOneSharpFloor
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249.Shared (mobiusMersenneTerm mobiusMersenneTheta)
/-- The truncation `t_Y(r) = ∑_{d = 1}^{Y} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne rung `r` to its first `Y` atoms. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n
/-- The quotient `Q(e, Y) = t_Y(e + 2) ^ 2 / t_Y(2 e + 2)` of Möbius-Mersenne prefixes, called the positive rank-one strict-subrank quotient in the surrounding development. The definition imposes neither positivity nor any admissibility condition: at `Y = 0` both prefixes are empty sums and the Lean division returns `0`. The theorems below restrict to `e ≥ 1` and `Y ≥ 4`. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)
end PalomarCorpus.E249.RankOneSharpFloor

namespace PalomarCorpus.E249.ResidueClassTotientSeries
/-- The binary value `∑_{n ≥ 0} a(n) / 2 ^ n` of an integer coefficient sequence `a`, with the terms cast from `ℤ` to `ℝ`. -/
noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n
/-- The binary value `∑_{n ≥ 0} f(φ(n) mod m) / 2 ^ n` of a fixed-resolution observable of the totient word, where `f` is an integer-valued letter map on residues and `m` is the fixed resolution. -/
noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n
/-- The least-residue totient series `A_m = ∑_{n ≥ 0} (φ(n) mod m) / 2 ^ n`, using least nonnegative residues. -/
noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n
end PalomarCorpus.E249.ResidueClassTotientSeries

namespace PalomarCorpus.E249.TermwiseDyadicVacuous
end PalomarCorpus.E249.TermwiseDyadicVacuous

namespace PalomarCorpus.E249.TotientAffineModeEscape
open scoped BigOperators
export PalomarCorpus.E249.Shared (totientBlock)
/-- The signed endpoint error `E_H = totientBlock H c - k (2 ^ H - 1)` of the totient block at basepoint `c` against a fixed quotient `k`, on the pure dyadic axis where the odd part of the candidate denominator is `1`. -/
noncomputable def pureDyadicEndpointError (H c : ℕ) (k : ℤ) : ℤ :=
  totientBlock H c - k * ((2 : ℤ) ^ H - 1)
/-- The property that the endpoint error is eventually an affine function of the height: there are integers `A` and `B` and a threshold `H0` with `E_H = A H + B` for every `H ≥ H0`. -/
noncomputable def EventuallyAffinePureDyadicEndpointError (c : ℕ) (k : ℤ) : Prop :=
  ∃ A B : ℤ, ∃ H0 : ℕ, ∀ H, H0 ≤ H →
    pureDyadicEndpointError H c k = A * H + B
end PalomarCorpus.E249.TotientAffineModeEscape

namespace PalomarCorpus.E249.TotientKernelBasis
open Module
/-- The base-`k` kernel channel `n ↦ φ(k ^ j n + r)` at level `j` and residue `r`, with values in `ℚ` through the cast from `ℕ`. -/
noncomputable def kernelSeq (k j r : ℕ) : ℕ → ℚ := fun n =>
  (Nat.totient (k ^ j * n + r) : ℚ)
/-- Index type for the canonical base-`k` family through level `e`: two zero-residue channels, and at each level `j + 1` with `j < e` one channel per pair `(s, u)` with `s < k ^ j` and `u < k - 1`, which parametrises exactly the residues `1 ≤ r < k ^ (j + 1)` with `k` not dividing `r`. -/
noncomputable abbrev CanonicalIndex (k e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)
/-- The canonical residue `k s + (u + 1)` named by a positive-level index `⟨j, (s, u)⟩`. The retained condition is that `k` does not divide the residue, which at a composite base is weaker than the residue being coprime to `k`. -/
noncomputable def canonicalResidue (k : ℕ) {e : ℕ}
    (x : Σ j : Fin e, Fin (k ^ j.val) × Fin (k - 1)) : ℕ :=
  k * x.2.1.val + (x.2.2.val + 1)
/-- The canonical level-`e` family of base-`k` totient channels: a left index `i ∈ Fin 2` gives `n ↦ φ(k ^ i n)`, and a right index `x` at level `j + 1` gives `n ↦ φ(k ^ (j + 1) n + canonicalResidue k x)`. -/
noncomputable def canonicalFamily (k e : ℕ) : CanonicalIndex k e → ℕ → ℚ
  | Sum.inl i => kernelSeq k i.val 0
  | Sum.inr x => kernelSeq k (x.1.val + 1) (canonicalResidue k x)
/-- Index type for the complete unreduced base-`k` kernel through level `e`: all pairs `⟨j, r⟩` with `j ≤ e` and `r < k ^ j`, so the type has `1 + k + ⋯ + k ^ e` elements. -/
noncomputable abbrev ThroughLevelIndex (k e : ℕ) := Σ j : Fin (e + 1), Fin (k ^ j.val)
/-- The complete unreduced family of base-`k` totient channels through level `e`, sending `⟨j, r⟩` to `n ↦ φ(k ^ j n + r)`. -/
noncomputable def throughLevelFamily (k e : ℕ) : ThroughLevelIndex k e → ℕ → ℚ
  | ⟨j, r⟩ => kernelSeq k j.val r.val
/-- The `ℚ`-linear evaluation map sending a formal combination of the `1 + k + ⋯ + k ^ e` unreduced channel symbols to the corresponding function `ℕ → ℚ`. Its kernel is the module of `ℚ`-linear relations among those channels. -/
noncomputable def relationMap (k e : ℕ) :
    (ThroughLevelIndex k e → ℚ) →ₗ[ℚ] (ℕ → ℚ) :=
  Fintype.linearCombination ℚ (throughLevelFamily k e)
end PalomarCorpus.E249.TotientKernelBasis

namespace PalomarCorpus.E249.TotientRigidity
/-- The defect `g(n) - φ(n)` of a candidate integer coefficient sequence `g` against Euler's totient, taken in `ℤ`. -/
noncomputable def totientDefect (g : ℕ → ℤ) (n : ℕ) : ℤ := g n - (Nat.totient n : ℤ)
end PalomarCorpus.E249.TotientRigidity
