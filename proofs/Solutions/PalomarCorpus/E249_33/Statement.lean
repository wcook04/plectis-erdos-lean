/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_33

Every non-theorem declaration of `PalomarCorpus/E249_33/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open ArithmeticFunction
open Filter Topology

namespace PalomarCorpus.E249_33.Shared
/-- The binary-weighted sum of the least nonnegative residues φ(n) modulo m. -/
noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n
end PalomarCorpus.E249_33.Shared

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
/-- The atom of index `n` at rung `r` of the Möbius-Mersenne ladder, namely `μ(n + 1) / (2 ^ (n + 1) - 1) ^ r` with `μ` the Möbius function; the index is shifted so that `n = 0` carries the divisor `d = 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) / (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The rung `Θ_r = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne ladder, defined as the real sum of the atoms above. The divisor convolution `φ = μ * id` gives `Θ_2 = S - 1/2` for the binary totient series `S = ∑_{n ≥ 1} φ(n) / 2 ^ n`. At `r = 0` the family is not summable and the Lean sum takes its default value `0`; every compared theorem uses the ladder only at `r ≥ 1`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The truncation `t_Y(r) = ∑_{d = 1}^{Y} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne rung `r` to its first `Y` atoms. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n
/-- The quotient `Q(e, Y) = t_Y(e + 2) ^ 2 / t_Y(2 e + 2)` of Möbius-Mersenne prefixes, called the positive rank-one strict-subrank quotient in the surrounding development. The definition imposes neither positivity nor any admissibility condition: at `Y = 0` both prefixes are empty sums and the Lean division returns `0`. The theorems below restrict to `e ≥ 1` and `Y ≥ 4`. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)
end PalomarCorpus.E249.RankOneSharpFloor

namespace PalomarCorpus.E249.RationalObservableClassification
open Filter Topology
open scoped BigOperators
export PalomarCorpus.E249_33.Shared (totientResidueValue)
end PalomarCorpus.E249.RationalObservableClassification

namespace PalomarCorpus.E249.ResidueClassTotientSeries
export PalomarCorpus.E249_33.Shared (totientResidueValue)
/-- The binary value `∑_{n ≥ 0} a(n) / 2 ^ n` of an integer coefficient sequence `a`, with the terms cast from `ℤ` to `ℝ`. -/
noncomputable def dyadicValue (a : ℕ → ℤ) : ℝ := ∑' n : ℕ, (a n : ℝ) / 2 ^ n
/-- The binary value `∑_{n ≥ 0} f(φ(n) mod m) / 2 ^ n` of a fixed-resolution observable of the totient word, where `f` is an integer-valued letter map on residues and `m` is the fixed resolution. -/
noncomputable def totientObservableValue (f : ℕ → ℤ) (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((f (Nat.totient n % m) : ℤ) : ℝ) / 2 ^ n
end PalomarCorpus.E249.ResidueClassTotientSeries

namespace PalomarCorpus.E249.TermwiseDyadicVacuous
end PalomarCorpus.E249.TermwiseDyadicVacuous

namespace PalomarCorpus.E249.TotientAffineModeEscape
open scoped BigOperators
/-- The binary block of `H` consecutive totient values starting at `N + 1`, most significant weight first: `∑_{j < H} φ(N + 1 + j) 2 ^ (H - 1 - j)`, an integer. It equals `2 ^ H R_N - R_{N + H}` for the binary totient tail `R_N`, and is `0` when `H = 0`. -/
noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)
/-- The signed endpoint error `E_H = totientBlock H c - k (2 ^ H - 1)` of the totient block at basepoint `c` against a fixed quotient `k`, on the pure dyadic axis where the odd part of the candidate denominator is `1`. -/
noncomputable def pureDyadicEndpointError (H c : ℕ) (k : ℤ) : ℤ :=
  totientBlock H c - k * ((2 : ℤ) ^ H - 1)
/-- The property that the endpoint error is eventually an affine function of the height: there are integers `A` and `B` and a threshold `H0` with `E_H = A H + B` for every `H ≥ H0`. -/
noncomputable def EventuallyAffinePureDyadicEndpointError (c : ℕ) (k : ℤ) : Prop :=
  ∃ A B : ℤ, ∃ H0 : ℕ, ∀ H, H0 ≤ H →
    pureDyadicEndpointError H c k = A * H + B
end PalomarCorpus.E249.TotientAffineModeEscape

namespace PalomarCorpus.E249.TotientRigidity
/-- The defect `g(n) - φ(n)` of a candidate integer coefficient sequence `g` against Euler's totient, taken in `ℤ`. -/
noncomputable def totientDefect (g : ℕ → ℤ) (n : ℕ) : ℤ := g n - (Nat.totient n : ℤ)
end PalomarCorpus.E249.TotientRigidity
