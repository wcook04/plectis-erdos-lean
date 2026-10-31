/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_31

Every non-theorem declaration of `PalomarCorpus/E249_31/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators

namespace PalomarCorpus.E249_31.Shared
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249_31.Shared

namespace PalomarCorpus.E249.ActualLcmOrbit
open scoped BigOperators
export PalomarCorpus.E249_31.Shared (totientTail)
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
export PalomarCorpus.E249_31.Shared (totientTail)
/-- The binary cyclotomic layer `|Φ_n(2)|`, the absolute value of the `n`th cyclotomic polynomial over `ℤ` evaluated at `2`, returned as a natural number through `Int.natAbs`. -/
noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs
/-- The property that a layer function `C` has unbounded prime support on the ray of multiples of `h`: for all bounds `B` and `N₀` there are primes `q ≥ N₀` and `p > B` with `p` dividing `C (h q)`. -/
noncomputable def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (h : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (h * q) ∧ B < p
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) -
      (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
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
/-- The shifted totient difference `φ(n + h) - φ(n)`, taken in `ℤ` through the cast from `ℕ`. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ :=
  (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The binary block of `H` consecutive totient values starting at `N + 1`, most significant weight first: `∑_{j < H} φ(N + 1 + j) 2 ^ (H - 1 - j)`, an integer. It equals `2 ^ H R_N - R_{N + H}` for the binary totient tail `R_N`, and is `0` when `H = 0`. -/
noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
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
