/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249

Erdős and Graham asked whether `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` is
irrational. The problem is open and nothing in this file decides it.

## Conditional structure under hypothetical rationality

`CarryRankFrontier`: if `S` is not irrational then one integral carry `u` with
multiplier `v > 0` has rational section rank at least `2 ^ e - 1` at every
depth `e` and is eventually periodic modulo `v` with one fixed positive
period. No theorem here turns eventual periodicity into a finite rank bound.

## Unconditional theorems about the totient

`TotientKernelBasis` and `DyadicTotientKernel`: for every base `k ≥ 2` and
depth `e ≥ 1` the base `k` kernel through level `e` has rank exactly
`k ^ e + 1`, with a canonical basis and the exact relation-module dimension.
Over `ℤ` the span of the unreduced channels has the canonical channels as a
basis, and the relation module has a basis of two-term reductions and rank
`∑_{j < e - 1} k ^ (j + 1)`.
Martin 2006 already implies the affine independence input; Coons 2010 owns
non-`k`-regularity of `φ`.

`ResidueClassTotientSeries`: `A_m = ∑ (φ(n) mod m) / 2 ^ n` is
irrational for every `m ≥ 3`, and for every `m ≥ 2` so is the series of
any integer letter map that vanishes at residue `0` and is nonzero at some
`r < m` with `r + 1` coprime to `m`. The mechanism is that of Erdős 1948.
The object is the reduced word, never `φ(n)`.

## Exact reformulations

`FullDepthRayAmplifier`, `CanonicalMersenneFrontier`, `ActualLcmOrbit` and
`BinaryCyclotomicAnchors` restate irrationality of `S` in four equivalent
coordinates. They supply no missing quantifier.

## Route closures and finite exclusions

`TotientAffineModeEscape` excludes one fixed affine endpoint-error mode.
`TermwiseDyadicVacuous`, `TotientRigidity`, `RankOneSharpFloor` and
`MobiusMersenneLadderStructure` close further named mechanisms.
`FareyWindowExclusion` and `PrefixTwoAdicExclusion` exclude finite ranges of
denominators with explicit bounds; they are not progress on irrationality.
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
/-- Unconditional identity: for every `a`, with `H = actualLcmHeight a`, the orbit value equals `2 ^ H (2 ^ H - 1) S - (Φ_{2 H} - Φ_H)`, where `S` is the real sum `∑' n, φ(n) / 2 ^ n` and `Φ` is the integer prefix. The orbit is therefore an integer translate of a scaled copy of the binary totient series. -/
theorem actualLcmTailOrbit_eq_scaled_totientSeries_sub_prefix (a : ℕ) :
    actualLcmTailOrbit a =
      (2 : ℝ) ^ actualLcmHeight a *
          ((2 : ℝ) ^ actualLcmHeight a - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) -
        ((totientPrefix (2 * actualLcmHeight a) : ℝ) -
          (totientPrefix (actualLcmHeight a) : ℝ)) := by
  sorry
/-- Exact reformulation: `∑' n, φ(n) / 2 ^ n` is irrational if and only if the LCM diagonal orbit is nonintegral cofinally often. The theorem exhibits no such index, so it decides nothing about the value of the series. -/
theorem irrational_totientSeries_iff_actualLcmOrbitNonintegralitySupply :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ↔
      PowerTwoActualLcmOrbitNonintegralitySupply := by
  sorry
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
/-- Unconditional: for every `h > 0` and every threshold `N₀` there are primes `q` and `p` with `p` coprime to `h q`, `p` dividing `|Φ_{h q}(2)|`, `h q` dividing `p - 1`, and `N₀ ≤ p - 1`. The mechanism is that the multiplicative order of `2` modulo such a `p` is exactly `h q`. The theorem produces the anchor only and supplies no window certificate. -/
theorem exists_clean_binaryCyclotomicAnchor
    (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ,
      q.Prime ∧
      p.Prime ∧
      Nat.Coprime p (h * q) ∧
      p ∣ binaryCyclotomicLayer (h * q) ∧
      h * q ∣ p - 1 ∧
      N₀ ≤ p - 1 := by
  sorry
/-- Unconditional: for every `h > 0` the binary cyclotomic layers have unbounded prime support along the ray `h q` with `q` prime, that is, for all `B` and `N₀` there are primes `q ≥ N₀` and `p > B` with `p` dividing `|Φ_{h q}(2)|`. -/
theorem binaryCyclotomicLayer_unboundedPrimeDivisorSupply
    (h : ℕ) (hh : 0 < h) :
    UnboundedPrimeDivisorSupply binaryCyclotomicLayer h := by
  sorry
/-- Exact reformulation: the anchored certificate supply for the binary cyclotomic layers holds if and only if `∑' n, φ(n) / 2 ^ n` is irrational. The clean anchors are proved unconditionally above, while the certified window discrepancy is the missing ingredient, so this equivalence decides nothing about the value of the series. -/
theorem binaryCyclotomicAnchoredKillSupply_iff_irrational :
    CyclotomicAnchoredKillSupply binaryCyclotomicLayer ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- Under the hypothesis that `∑' n, φ(n) / 2 ^ n` is not irrational, there is a period `h > 0` whose ray carries unbounded prime support in the binary cyclotomic layers while every tail difference `R_{N + h} - R_N` with `N` beyond one threshold is an integer. Unbounded prime support alone therefore cannot force the annihilation that irrationality would need. -/
theorem exists_unbounded_binaryCyclotomicSupport_with_periodLock_of_not_irrational
    (hrat : ¬ Irrational
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ h : ℕ, 0 < h ∧
      UnboundedPrimeDivisorSupply binaryCyclotomicLayer h ∧
      ∃ N₀ : ℕ, ∀ N, N₀ ≤ N →
        totientTail (N + h) - totientTail N ∈
          Set.range ((↑) : ℤ → ℝ) := by
  sorry
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
/-- Supporting exact recurrence: when `M` divides `2 ^ H - 1`, the canonical residue at basepoint `N + 1` equals `(2 · fullMersenneBlockResidue H N M - (φ(N + 1 + H) - φ(N + 1))) mod M`. This is the finite dynamical system used to search for the centred gap. -/
theorem fullMersenneBlockResidue_succ
    {H N M : ℕ} (hM : M ∣ 2 ^ H - 1) :
    fullMersenneBlockResidue H (N + 1) M =
      (2 * fullMersenneBlockResidue H N M -
        deltaTotient H (N + 1)) % (M : ℤ) := by
  sorry
/-- Supporting reduction: the canonical basepoint supply, in which the basepoint is pinned at `c`, implies the apparently stronger cofinal supply in which the basepoint may move beyond any threshold. The converse implication is not part of this statement. -/
theorem fullMersenneCenteredResidueGapSupply_of_canonicalBasepoint
    (hsupply : FullMersenneCanonicalBasepointResidueGapSupply) :
    FullMersenneCenteredResidueGapSupply := by
  sorry
/-- Exact reformulation: the canonical basepoint centred-gap supply holds if and only if `∑' n, φ(n) / 2 ^ n` is irrational. No construction supplies the required `H`, so the equivalence records the remaining arithmetic obligation and decides nothing about the value of the series. -/
theorem fullMersenneCanonicalBasepointResidueGapSupply_iff_irrational :
    FullMersenneCanonicalBasepointResidueGapSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
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
/-- For any coefficient sequence bounded by its index, `c n ≤ n` for every `n`, the binary value `binaryCoeffSeries c` fails to be irrational if and only if there are `v > 0` and `u : ℕ → ℤ` with `IsTemperedBinaryOrbit c v u`. This converts a statement about a real number into a statement about an integer sequence. -/
theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit c v u := by
  sorry
/-- Supporting channel recovery: for a tempered integral carry `u` of `Nat.totient` with multiplier `v`, any level `j` and any residue `r > 0`, the scaled totient section `n ↦ v φ(2 ^ j n + r)` equals `n ↦ 2 u (2 ^ j n + r - 1) - u (2 ^ j n + r)` as functions `ℕ → ℚ`, so every positive-residue totient channel is recovered from two adjacent carry sections. -/
theorem totient_carryKernel_diff
    {v : ℕ} {u : ℕ → ℤ}
    (hu : IsTemperedBinaryOrbit Nat.totient v u)
    {j r : ℕ} (hr : 0 < r) :
    (fun n => (v : ℚ) * totientKernelSeq j r n) =
      fun n => 2 * carryKernelSeq u j (r - 1) n -
        carryKernelSeq u j r n := by
  sorry
/-- Supporting rank transport: given `v > 0`, a tempered integral carry `u` of `Nat.totient` with multiplier `v`, a depth `e`, and a separated minor certificate for the canonical totient family at depth `e`, the `ℚ`-span of the carry sections through depth `e` has `finrank` at least `2 ^ e - 1`. -/
theorem finrank_canonicalCarryKernel_ge_of_certificate
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (e : ℕ)
    (cert : SeparatedMinorCertificate (canonicalTotientKernelFamily e)) :
    2 ^ e - 1 ≤
      Module.finrank ℚ
        (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := by
  sorry
/-- If the binary totient series is not irrational, then there are `v > 0` and a tempered integral carry `u` of `Nat.totient` with multiplier `v` such that for every depth `e` the `ℚ`-span of its canonical carry sections has `finrank` at least `2 ^ e - 1`. The statement carries no certificate hypothesis; `hirr` is its only hypothesis. -/
theorem not_irrational_totientSeries_implies_unbounded_carryRank_unconditional
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        ∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e))) := by
  sorry
/-- Supporting bridge: for a tempered integral carry `u` of `Nat.totient` with multiplier `v > 0`, the integer `v` divides `u (N + k) - u N` if and only if the tail difference `R_{N + k} - R_N` lies in the image of `ℤ` in `ℝ`. -/
theorem carryShift_dvd_iff_tailDiff_mem_int
    {v : ℕ} {u : ℕ → ℤ} (hv : 0 < v)
    (hu : IsTemperedBinaryOrbit Nat.totient v u) (N k : ℕ) :
    (v : ℤ) ∣ u (N + k) - u N ↔
      totientTail (N + k) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- The principal conditional theorem: if the binary totient series is not irrational, then one and the same tempered integral carry `u`, with some multiplier `v > 0`, has `ℚ`-section `finrank` at least `2 ^ e - 1` at every depth `e` and is eventually periodic modulo `v` with one fixed positive period `h` beyond one threshold `N₀`. No theorem here turns eventual periodicity into a finite rational rank, so no contradiction and no irrationality statement follows. -/
theorem not_irrational_totientSeries_implies_mod_period_and_unbounded_rank
    (hirr : ¬ Irrational (binaryCoeffSeries Nat.totient)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ,
          2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ
                (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := by
  sorry
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
/-- Unconditional structure theorem for the dyadic kernel of Euler's totient: the odd-core family is `ℚ`-linearly independent, its `ℚ`-span equals the span of the full dyadic kernel, and for every `e ≥ 1` the span of the complete unreduced family through level `e` equals the span of the canonical family and has `finrank` exactly `2 ^ e + 1`. It is a statement about the coefficient sequence and says nothing about the value of the binary totient series. -/
theorem dyadicTotientKernelOddCoreBasisAndFiniteRanks :
    LinearIndependent ℚ oddCoreTotientKernelFamily ∧
      Submodule.span ℚ (Set.range fullTotientKernelFamily) =
        Submodule.span ℚ (Set.range oddCoreTotientKernelFamily) ∧
      ∀ e : ℕ, 1 ≤ e →
        Submodule.span ℚ
            (Set.range (totientKernelThroughLevelFamily e)) =
          Submodule.span ℚ
            (Set.range (canonicalTotientKernelFamily e)) ∧
        finrank ℚ
            (Submodule.span ℚ
              (Set.range (totientKernelThroughLevelFamily e))) = 2 ^ e + 1 := by
  sorry
end PalomarCorpus.E249.DyadicTotientKernel

namespace PalomarCorpus.E249.FareyWindowExclusion
/-- The explicit denominator bound `79639646646701375323355774875831053`, about `7.96 · 10 ^ 34`, reached by the Farey window computation. -/
def fareyDenBound : ℕ := 79639646646701375323355774875831053
/-- Finite exclusion: for every integer `a` and every natural `d` with `0 < d ≤ fareyDenBound`, the real number `∑' n, φ(n) / 2 ^ n` is different from `a / d`. This excludes a finite range of denominators and is not a proof of irrationality. -/
theorem farey_int_exclusion :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ fareyDenBound →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (a : ℝ) / (d : ℝ) := by
  sorry
/-- Finite exclusion in rational form: no rational `p` whose reduced denominator `p.den` is at most `fareyDenBound` equals `∑' n, φ(n) / 2 ^ n`. Rationals with larger denominators are untouched, so this is not a proof of irrationality. -/
theorem farey_rat_exclusion :
    ∀ p : ℚ, p.den ≤ fareyDenBound →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  sorry
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
/-- Amplification from one seed: if `d > 0` and a single certificate `certifiedKill d N L` holds, then there is `T > 0` such that every `t ≥ T` admits a full-depth multiplier `m` with `t ≤ m ≤ t + 1`, so the full-depth multipliers meet every sufficiently late pair of consecutive integers. -/
theorem eventually_twoSyndetic_fullDepthKillMultipliers_of_seed
    {d N L : ℕ} (hd : 0 < d) (hseed : certifiedKill d N L) :
    ∃ T : ℕ, 0 < T ∧ ∀ t : ℕ, T ≤ t →
      ∃ m : ℕ, m ∈ fullDepthKillMultipliers d N ∧ t ≤ m ∧ m ≤ t + 1 := by
  sorry
/-- Exact criterion on one ray: for `d > 0` there is `t > 0` with `certifiedKill (t d) N (t d)` if and only if the tail difference `R_{N + d} - R_N` lies outside the image of `ℤ` in `ℝ`. -/
theorem exists_fullDepthKill_on_ray_iff_shift_notMem_int
    {d N : ℕ} (hd : 0 < d) :
    (∃ t : ℕ, 0 < t ∧ certifiedKill (t * d) N (t * d)) ↔
      totientTail (N + d) - totientTail N ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- Exact reformulation: the full-depth escape statement holds if and only if `∑' n, φ(n) / 2 ^ n` is irrational. -/
theorem apFullDepthEscape_iff_irrational :
    ApFullDepthEscape ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- Supporting equivalence: the cofinal full-depth supply and the period-multiple supply, whose window lengths are unconstrained, are the same statement. -/
theorem cofinalFullDepthKillSupply_iff_periodMultipleKillSupply :
    CofinalFullDepthKillSupply ↔ PeriodMultipleKillSupply := by
  sorry
/-- Exact reformulation: the cofinal full-depth supply holds if and only if `∑' n, φ(n) / 2 ^ n` is irrational. Neither direction exhibits a certificate, so the value of the series is not decided. -/
theorem cofinalFullDepthKillSupply_iff_irrational :
    CofinalFullDepthKillSupply ↔
      Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
end PalomarCorpus.E249.FullDepthRayAmplifier

namespace PalomarCorpus.E249.MobiusMersenneLadderStructure
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249.Shared (mobiusMersenneTerm mobiusMersenneTheta)
/-- Unconditional: for every rung `r ≥ 1` the Möbius-Mersenne ladder is strictly log-concave, `Θ_r Θ_{r + 2} < Θ_{r + 1} ^ 2`. The moment sequence of a nonnegative measure has nonnegative order-two Hankel determinants, so the ladder admits no such representation. -/
theorem mobiusMersenneTheta_strict_logConcave (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) <
      mobiusMersenneTheta (r + 1) ^ 2 := by
  sorry
/-- The same fact written as strict negativity of the shifted order-two Hankel determinant, `Θ_r Θ_{r + 2} - Θ_{r + 1} ^ 2 < 0` for every `r ≥ 1`. It bounds no higher-order determinant and no Hankel rank. -/
theorem mobiusMersenneTheta_hankel_two_neg (r : ℕ) (hr : 1 ≤ r) :
    mobiusMersenneTheta r * mobiusMersenneTheta (r + 2) -
      mobiusMersenneTheta (r + 1) ^ 2 < 0 := by
  sorry
end PalomarCorpus.E249.MobiusMersenneLadderStructure

namespace PalomarCorpus.E249.PrefixTwoAdicExclusion
/-- The integer prefix `P_n = ∑_{i < n} 2 ^ (n - 1 - i) φ(i + 1)` of `2 ^ n S`, written over the first `n` positive arguments; `P_0 = 0`. -/
noncomputable def totientPrefix (n : ℕ) : ℕ :=
  ∑ i ∈ Finset.range n, 2 ^ (n - 1 - i) * Nat.totient (i + 1)
/-- Supporting recurrence: `P_{n + 1} = 2 P_n + φ(n + 1)`. -/
theorem totientPrefix_succ (n : ℕ) :
    totientPrefix (n + 1) = 2 * totientPrefix n + Nat.totient (n + 1) := by
  sorry
/-- Supporting identity: `P_n = ∑_{i ≤ n} φ(i) 2 ^ (n - i)`, the form used elsewhere in this file and in the shared namespace; the two agree because `φ(0) = 0`. -/
theorem totientPrefix_eq_corpusForm (n : ℕ) :
    totientPrefix n = ∑ i ∈ Finset.range (n + 1), Nat.totient i * 2 ^ (n - i) := by
  sorry
/-- The local tail `R_n = 2 ^ n S - P_n` of an arbitrary real number `S` against the totient prefix. It is stated for a general `S` so that the exclusion theorems below can carry a rational form for `S` as an explicit hypothesis. -/
noncomputable def prefixTail (S : ℝ) (n : ℕ) : ℝ :=
  2 ^ n * S - (totientPrefix n : ℝ)
/-- Supporting integrality: if `S = a / (2 ^ c v)` with `v > 0` and `c ≤ n`, then `v · prefixTail S n` is the integer `2 ^ (n - c) a - v P_n`. -/
theorem oddPart_mul_prefixTail_eq_intCast
    {S : ℝ} {a : ℤ} {c v n : ℕ} (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ))) (hcn : c ≤ n) :
    (v : ℝ) * prefixTail S n
      = (((2 : ℤ) ^ (n - c) * a - (v : ℤ) * (totientPrefix n : ℤ) : ℤ) : ℝ) := by
  sorry
/-- Finite exclusion step: if `S = a / (2 ^ c v)` with `v` odd and positive, the local tail `R_n` is positive, `c + t ≤ n`, and `2 ^ t` divides `P_n`, then `2 ^ t ≤ v R_n`. One exact power of two dividing the prefix therefore constrains the admissible denominators. -/
theorem prefix_twoAdic_denominator_exclusion
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * prefixTail S n := by
  sorry
/-- The same finite exclusion with the tail bound inserted as a hypothesis: if `S = a / (2 ^ c v)` with `v` odd and positive, the local tail satisfies `0 < R_n ≤ n + 2`, `c + t ≤ n`, and `2 ^ t` divides `P_n`, then `2 ^ t ≤ v (n + 2)`. -/
theorem prefix_twoAdic_denominator_lower_bound
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t ≤ (v : ℝ) * ((n : ℝ) + 2) := by
  sorry
/-- The same finite exclusion read as a floor on the odd part of the denominator: if `S = a / (2 ^ c v)` with `v` odd and positive, `0 < R_n ≤ n + 2`, `c + t ≤ n`, and `2 ^ t` divides `P_n`, then `2 ^ t / (n + 2) ≤ v`. This excludes a finite rectangle of candidate denominators `2 ^ c v` and is not a proof of irrationality. -/
theorem prefix_twoAdic_odd_denominator_floor
    {S : ℝ} {a : ℤ} {c v n t : ℕ}
    (hvodd : Odd v) (hvpos : 0 < v)
    (hS : S = (a : ℝ) / (2 ^ c * (v : ℝ)))
    (hpos : 0 < prefixTail S n)
    (htail : prefixTail S n ≤ (n : ℝ) + 2)
    (hct : c + t ≤ n)
    (hdvd : 2 ^ t ∣ totientPrefix n) :
    (2 : ℝ) ^ t / ((n : ℝ) + 2) ≤ (v : ℝ) := by
  sorry
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
/-- Sharp minimum: on the admissible range `e ≥ 1` and `Y ≥ 4`, `Q(1, 5) ≤ Q(e, Y)`, so the five-atom first-depth kernel minimises the quotient. -/
theorem rankOneSubrankQuotient_ge_one_five
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient 1 5 ≤ rankOneSubrankQuotient e Y := by
  sorry
/-- Uniqueness of the minimiser: on the admissible range `e ≥ 1` and `Y ≥ 4`, `Q(e, Y) = Q(1, 5)` holds exactly when `e = 1` and `Y = 5`. -/
theorem rankOneSubrankQuotient_eq_one_five_iff
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    rankOneSubrankQuotient e Y = rankOneSubrankQuotient 1 5 ↔
      e = 1 ∧ Y = 5 := by
  sorry
/-- Sharp separation: on the admissible range `e ≥ 1` and `Y ≥ 4`, `Q(e, Y)` exceeds the rung `Θ_2 = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ 2` by more than `21 / 320`. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt_twentyOne_div_threeTwenty
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (21 : ℝ) / 320 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  sorry
/-- The same separation stated with the unit-fraction floor `1 / 16`, valid on the whole admissible range `e ≥ 1`, `Y ≥ 4`. -/
theorem rankOneSubrankQuotient_sub_theta_two_gt_one_div_sixteen
    {e Y : ℕ} (he : 1 ≤ e) (hY : 4 ≤ Y) :
    (1 : ℝ) / 16 <
      rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  sorry
/-- Sharpness of the unit-fraction floor: the universally quantified bound `Q(e, Y) - Θ_2 > 1 / 15` over the admissible range is false, so `1 / 16` is the largest unit fraction that works. The statement is the negation of that quantified inequality. -/
theorem not_forall_rankOneSubrankQuotient_sub_theta_two_gt_one_div_fifteen :
    ¬ ∀ {e Y : ℕ}, 1 ≤ e → 4 ≤ Y →
      (1 : ℝ) / 15 <
        rankOneSubrankQuotient e Y - mobiusMersenneTheta 2 := by
  sorry
/-- Closure under positive mixing: for a nonempty finite index set `s`, strictly positive weights `w i` and admissible pairs `(e i, Y i)` for `i ∈ s`, the weighted mean of the quotients still exceeds `Θ_2` by more than `21 / 320`, so no positive combination of rank-one blocks approaches `Θ_2`. -/
theorem positive_direct_sum_sub_theta_two_gt_twentyOne_div_threeTwenty
    {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (hs : s.Nonempty)
    (w : ι → ℝ) (e Y : ι → ℕ)
    (hw : ∀ i ∈ s, 0 < w i)
    (he : ∀ i ∈ s, 1 ≤ e i)
    (hY : ∀ i ∈ s, 4 ≤ Y i) :
    (21 : ℝ) / 320 <
      (∑ i ∈ s, w i * rankOneSubrankQuotient (e i) (Y i)) /
          (∑ i ∈ s, w i) -
        mobiusMersenneTheta 2 := by
  sorry
/-- Rational linear-form obstruction: if an admissible quotient satisfies `Q(e, Y) = p / q` with `q ≥ 1`, then `|q Θ_2 - p| > 21 q / 320`. Such an approximant stays far from `Θ_2` in the linear-form scale, so it cannot belong to a sequence witnessing irrationality. -/
theorem primitive_form_abs_gt_twentyOne_div_threeTwenty
    {e Y q : ℕ} {p : ℤ}
    (he : 1 ≤ e) (hY : 4 ≤ Y) (hq : 1 ≤ q)
    (hquot : rankOneSubrankQuotient e Y = (p : ℝ) / q) :
    (q : ℝ) * (21 : ℝ) / 320 <
      |(q : ℝ) * mobiusMersenneTheta 2 - p| := by
  sorry
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
/-- Quantitative Diophantine core: let `a` be an integer sequence with `|a n| ≤ C`, let `q ≥ 1` satisfy `2 q C < 2 ^ L`, and suppose `a (N + 1 + L) = t` with `t ≠ 0` while `a (N + 1 + i) = 0` for every `i ≤ 2 L` with `i ≠ L`. Then every integer `k` satisfies `q (|t| - C / 2 ^ L) / 2 ^ (N + 1 + L) ≤ |q · dyadicValue a - k|`. One isolated nonzero letter inside a two-sided block of zeros keeps `q` times the value away from every integer. -/
theorem isolated_pulse_separation {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    {N L q : ℕ} {t : ℤ} (hq : 1 ≤ q) (hL : 2 * (q : ℝ) * C < 2 ^ L)
    (hcentre : a (N + 1 + L) = t) (ht : t ≠ 0)
    (hzero : ∀ i, i ≤ 2 * L → i ≠ L → a (N + 1 + i) = 0) (k : ℤ) :
    (q : ℝ) * (|(t : ℝ)| - C / 2 ^ L) / 2 ^ (N + 1 + L)
      ≤ |(q : ℝ) * dyadicValue a - (k : ℝ)| := by
  sorry
/-- Number-theory-free irrationality criterion: a bounded integer coefficient sequence whose support carries arbitrarily long two-sided isolated pulses has irrational binary value. The pulse hypothesis asks that for every `L` there be `p > L + 1` with `a p ≠ 0` and `a (p - j) = a (p + j) = 0` for every `0 < j ≤ L`. -/
theorem irrational_dyadicValue_of_pulses {a : ℕ → ℤ} {C : ℝ} (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L : ℕ, ∃ p : ℕ, L + 1 < p ∧ a p ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (p - j) = 0 ∧ a (p + j) = 0) :
    Irrational (dyadicValue a) := by
  sorry
/-- Arithmetic supply: for `m ≥ 2` and any residue `r` with `r + 1` coprime to `m`, and for any `L` and `N`, there is a prime `p` with `p > N`, `p > L + 1`, `φ(p) ≡ r` modulo `m`, and `m` dividing both `φ(p - j)` and `φ(p + j)` for every `0 < j ≤ L`. The proof combines the Chinese remainder theorem with Dirichlet's theorem on primes in arithmetic progressions. -/
theorem two_sided_prime_isolation {m : ℕ} (hm : 2 ≤ m) (L N r : ℕ)
    (hr : Nat.Coprime (r + 1) m) :
    ∃ p : ℕ, N < p ∧ L + 1 < p ∧ p.Prime ∧ Nat.totient p ≡ r [MOD m] ∧
      ∀ j, 0 < j → j ≤ L → m ∣ Nat.totient (p - j) ∧ m ∣ Nat.totient (p + j) := by
  sorry
/-- Unconditional irrationality for fixed-resolution observables: if `m ≥ 2`, the letter map `f` vanishes at residue `0`, and some residue `r < m` with `r + 1` coprime to `m` has `f r ≠ 0`, then `∑_n f(φ(n) mod m) / 2 ^ n` is irrational. The object is the reduced word `φ(n) mod m` rather than `φ(n)` itself. -/
theorem irrational_totientObservable {m : ℕ} (hm : 2 ≤ m) (f : ℕ → ℤ) (hf0 : f 0 = 0)
    {r : ℕ} (hr : r < m) (hcop : Nat.Coprime (r + 1) m) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f m) := by
  sorry
/-- Dyadic resolution case: at resolution `m = 2 ^ k` with `k ≥ 1`, every integer-valued letter map that vanishes at residue `0` and is nonzero at some even residue `r < 2 ^ k` has irrational binary value. Every even residue qualifies because `r + 1` is then odd and hence coprime to `2 ^ k`. -/
theorem fixed_resolution_observable_irrational {k : ℕ} (hk : 1 ≤ k) (f : ℕ → ℤ)
    (hf0 : f 0 = 0) {r : ℕ} (hr : r < 2 ^ k) (hreven : r % 2 = 0) (hfr : f r ≠ 0) :
    Irrational (totientObservableValue f (2 ^ k)) := by
  sorry
/-- Headline unconditional consequence: for every `m ≥ 3` the least-residue totient series `A_m = ∑_n (φ(n) mod m) / 2 ^ n` is irrational. The excluded small cases are rational, `A_1 = 0` and `A_2 = 3 / 4`, a fact not formalised here. -/
theorem residue_series_irrational {m : ℕ} (hm : 3 ≤ m) :
    Irrational (totientResidueValue m) := by
  sorry
end PalomarCorpus.E249.ResidueClassTotientSeries

namespace PalomarCorpus.E249.TermwiseDyadicVacuous
/-- Route closure: whenever `t ≥ 1`, `N + t ≥ 2`, `v ≥ 1` and `2 ^ t` divides `φ(N + t)`, one has `2 ^ t ≤ v (N + t + 2)`. The termwise dyadic window therefore never beats the size budget and excludes no denominator, because `2 ^ t ∣ φ(N + t)` already forces `2 ^ t ≤ φ(N + t) < N + t`. -/
theorem termwise_dyadic_window_vacuous
    {N t v : ℕ} (ht : 1 ≤ t) (hNt : 2 ≤ N + t) (hv : 1 ≤ v)
    (hdvd : 2 ^ t ∣ Nat.totient (N + t)) :
    2 ^ t ≤ v * (N + t + 2) := by
  sorry
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
/-- Unconditional route closure: for every basepoint `c` and every fixed quotient `k`, the endpoint error is not eventually affine in the height. An affine tail would force the shifted totient letters onto one affine line, which fails at the exact points `(p, p - 1)`, `(q, q - 1)` and `(2 p, p - 1)` for arbitrarily late primes `2 < p < q`. This excludes one fixed endpoint-error mode; it does not exclude every mechanism by which the binary totient series could be rational. -/
theorem not_eventuallyAffine_pureDyadicEndpointError (c : ℕ) (k : ℤ) :
    ¬ EventuallyAffinePureDyadicEndpointError c k := by
  sorry
end PalomarCorpus.E249.TotientAffineModeEscape

namespace PalomarCorpus.E249.TotientKernelBasis
open Module
/-- All-slope affine independence: for a finite index type and affine forms `a i · n + b i` with `a i > 0` and `b i > 0` that are pairwise non-proportional, meaning `a i · b j ≠ a j · b i` whenever `i ≠ j`, the sequences `n ↦ φ(a i n + b i)` are linearly independent over `ℚ`. No parity, primitivity or coprimality hypothesis is imposed. Martin's 2006 theorem already implies this conclusion; the proof here is an independent finite-determinant argument, a square evaluation minor made diagonal modulo one auxiliary prime chosen through the Chinese remainder theorem and Dirichlet's theorem on primes in arithmetic progressions. -/
theorem allSlopeAffineTotientFormsLinearIndependent
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a b : ι → ℕ) (ha : ∀ i, 0 < a i) (hb : ∀ i, 0 < b i)
    (hcross : ∀ i j, i ≠ j → a i * b j ≠ a j * b i) :
    LinearIndependent ℚ (fun (i : ι) (n : ℕ) => (Nat.totient (a i * n + b i) : ℚ)) := by
  sorry
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
/-- Unconditional all-base structure theorem: for every base `k ≥ 2` and depth `e ≥ 1`, the canonical family is `ℚ`-linearly independent, it spans the same subspace as the complete unreduced family through level `e`, that span therefore carries a basis indexed by the canonical index, its `finrank` is exactly `k ^ e + 1`, and the relation module has `finrank` exactly `∑_{1 ≤ j < e} k ^ j`. The last clause gives the dimension of the relation space and does not claim that any named family of relations generates it. -/
theorem allBaseTotientKernelBasisRankAndRelationDimension
    (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalFamily k e) ∧
      Submodule.span ℚ (Set.range (throughLevelFamily k e)) =
        Submodule.span ℚ (Set.range (canonicalFamily k e)) ∧
      Nonempty (Basis (CanonicalIndex k e) ℚ
        (Submodule.span ℚ (Set.range (throughLevelFamily k e)))) ∧
      finrank ℚ (Submodule.span ℚ (Set.range (throughLevelFamily k e))) =
        k ^ e + 1 ∧
      finrank ℚ (LinearMap.ker (relationMap k e)) =
        ∑ j ∈ Finset.Ico 1 e, k ^ j := by
  sorry
/-- The `ℤ`-linear span, inside the functions `ℕ → ℚ`, of the complete unreduced base-`k` family through level `e`. -/
noncomputable abbrev IntegralChannelSpan (k e : ℕ) :=
  Submodule.span ℤ (Set.range (throughLevelFamily k e))
/-- The unreduced channel retained for each canonical index: a left index `i` gives the zero-residue channel `⟨i, 0⟩`, and a right index `x` at level `j + 1` gives the channel `⟨j + 1, canonicalResidue k x⟩`. The hypotheses `2 ≤ k` and `1 ≤ e` supply the bounds that make these valid indices. -/
noncomputable def retainedChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    CanonicalIndex k e → ThroughLevelIndex k e
  | Sum.inl i =>
      ⟨⟨i.val, by have hi := i.isLt; omega⟩,
        ⟨0, pow_pos (by omega : 0 < k) _⟩⟩
  | Sum.inr x =>
      ⟨⟨x.1.val + 1, by have hx := x.1.isLt; omega⟩,
        ⟨canonicalResidue k x, by
          show k * x.2.1.val + (x.2.2.val + 1) < k ^ (x.1.val + 1)
          have hs : x.2.1.val + 1 ≤ k ^ x.1.val := x.2.1.isLt
          have hu : x.2.2.val < k - 1 := x.2.2.isLt
          calc k * x.2.1.val + (x.2.2.val + 1) < k * x.2.1.val + k := by omega
            _ = k * (x.2.1.val + 1) := by ring
            _ ≤ k * k ^ x.1.val := Nat.mul_le_mul_left k hs
            _ = k ^ (x.1.val + 1) := by ring⟩⟩
/-- The unreduced channel indices through level `e` that are not retained channels. -/
noncomputable abbrev OmittedIntegralChannel (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :=
  { i : ThroughLevelIndex k e // i ∉ Set.range (retainedChannel k e hk he) }
/-- The `ℤ`-linear evaluation sending a finitely supported integer combination of the unreduced channel symbols through level `e` to the corresponding element of their integral span. -/
noncomputable def integralChannelEvaluation (k e : ℕ) :
    (ThroughLevelIndex k e →₀ ℤ) →ₗ[ℤ] IntegralChannelSpan k e :=
  Finsupp.linearCombination ℤ
    (fun i => (⟨throughLevelFamily k e i, Submodule.subset_span ⟨i, rfl⟩⟩ :
      IntegralChannelSpan k e))
/-- The module of integer relations among the unreduced channels through level `e`, the kernel of the integral evaluation. -/
noncomputable abbrev IntegralRelations (k e : ℕ) :=
  LinearMap.ker (integralChannelEvaluation k e)
/-- Integral normal form of the base-`k` totient kernel through level `e`, for `k ≥ 2` and `e ≥ 1`. The integral span of the unreduced channels has a `ℤ`-basis indexed by the canonical index whose vectors are the canonical channels. The relation module has a `ℤ`-basis indexed by the omitted channels whose vectors are two-term reductions: for every omitted channel `o` there are a canonical index `j` and a natural number `a` such that channel `o` equals `a` times canonical channel `j` and the basis vector at `o` is the symbol of `o` minus `a` times the symbol of the retained channel of `j`. The relation module has rank `∑_{j < e - 1} k ^ (j + 1)` over `ℤ`. -/
theorem displayed_integral_normal_form (k e : ℕ) (hk : 2 ≤ k) (he : 1 ≤ e) :
    (∃ c : Basis (CanonicalIndex k e) ℤ (IntegralChannelSpan k e),
      ∀ i, (c i : ℕ → ℚ) = canonicalFamily k e i) ∧
    (∃ b : Basis (OmittedIntegralChannel k e hk he) ℤ (IntegralRelations k e),
      ∀ o, ∃ j : CanonicalIndex k e, ∃ a : ℕ,
        throughLevelFamily k e o.val = (a : ℤ) • canonicalFamily k e j ∧
        (b o : ThroughLevelIndex k e →₀ ℤ) =
          Finsupp.single o.val 1 - Finsupp.single (retainedChannel k e hk he j) (a : ℤ)) ∧
    finrank ℤ (IntegralRelations k e) =
      ∑ j ∈ Finset.range (e - 1), k ^ (j + 1) := by
  sorry
end PalomarCorpus.E249.TotientKernelBasis

namespace PalomarCorpus.E249.TotientRigidity
/-- The defect `g(n) - φ(n)` of a candidate integer coefficient sequence `g` against Euler's totient, taken in `ℤ`. -/
noncomputable def totientDefect (g : ℕ → ℤ) (n : ℕ) : ℤ := g n - (Nat.totient n : ℤ)
/-- Supporting identity: `φ(p n) = p φ(n)` for a prime `p` dividing `n`, stated over `ℤ`. -/
theorem totient_prime_mul_of_dvd {p n : ℕ} (hp : p.Prime) (h : p ∣ n) :
    (Nat.totient (p * n) : ℤ) = (p : ℤ) * (Nat.totient n : ℤ) := by
  sorry
/-- Supporting identity: `φ(p n) = (p - 1) φ(n)` for a prime `p` not dividing `n`, stated over `ℤ`. -/
theorem totient_prime_mul_of_not_dvd {p n : ℕ} (hp : p.Prime) (h : ¬ p ∣ n) :
    (Nat.totient (p * n) : ℤ) = ((p : ℤ) - 1) * (Nat.totient n : ℤ) := by
  sorry
/-- Supporting identity: `φ(2 m) = φ(m)` for odd `m`, stated over `ℕ`. -/
theorem totient_two_mul_of_odd {m : ℕ} (hm : Odd m) :
    Nat.totient (2 * m) = Nat.totient m := by
  sorry
/-- Supporting identity: `φ(2 m) = 2 φ(m)` for even `m`, stated over `ℕ`; the degenerate case `m = 0` is included and both sides are `0`. -/
theorem totient_two_mul_of_even {m : ℕ} (hm : Even m) :
    Nat.totient (2 * m) = 2 * Nat.totient m := by
  sorry
/-- Rigidity route closure: let `p` be prime and let `g : ℕ → ℤ` obey the exact `p` laws `g(p n) = (p - 1) g(n)` when `p` does not divide `n` and `g(p n) = p g(n)` when `p` divides `n`, for every `n ≥ 1`, and suppose that for every `ε > 0` the bound `|g(n) - φ(n)| ≤ ε n` holds for all large `n`. Then `g(n) = φ(n)` for every `n ≥ 1`. One exact prime law with an `o(n)` error therefore leaves no rational control other than `φ` itself. -/
theorem one_prime_law_and_little_o_forces_totient
    {p : ℕ} (hp : p.Prime) {g : ℕ → ℤ}
    (hlaw_not_dvd : ∀ n : ℕ, 1 ≤ n → ¬ p ∣ n → g (p * n) = ((p : ℤ) - 1) * g n)
    (hlaw_dvd : ∀ n : ℕ, 1 ≤ n → p ∣ n → g (p * n) = (p : ℤ) * g n)
    (hsmall : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      |(g n : ℝ) - (Nat.totient n : ℝ)| ≤ ε * (n : ℝ))
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  sorry
/-- Rigidity route closure: let `g : ℕ → ℤ` satisfy `g(2 m) = g(m)` for odd `m ≥ 1` and `g(2 m) = 2 g(m)` for even `m ≥ 2`, and suppose that for every `q ≥ 1` the congruence `q ∣ g(n) - φ(n)` holds for all sufficiently large `n`. Then `g(n) = φ(n)` for every `n ≥ 1`. No odd-prime law and no size bound are needed. -/
theorem even_law_and_eventual_congruence_forces_totient
    {g : ℕ → ℤ}
    (hodd : ∀ m : ℕ, Odd m → 1 ≤ m → g (2 * m) = g m)
    (heven : ∀ m : ℕ, Even m → 2 ≤ m → g (2 * m) = 2 * g m)
    (hcong : ∀ q : ℕ, 1 ≤ q → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      (q : ℤ) ∣ totientDefect g n)
    {n : ℕ} (hn : 1 ≤ n) :
    g n = (Nat.totient n : ℤ) := by
  sorry
end PalomarCorpus.E249.TotientRigidity
