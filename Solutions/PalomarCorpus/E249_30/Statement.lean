/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_30

Every non-theorem declaration of `PalomarCorpus/E249_30/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Filter Topology
open Finset
open Matrix
open ArithmeticFunction

namespace PalomarCorpus.E249_30.Shared
/-- The atom of index `n` at rung `r` of the Möbius-Mersenne ladder, namely `μ(n + 1) / (2 ^ (n + 1) - 1) ^ r` with `μ` the Möbius function; the index is shifted so that `n = 0` carries the divisor `d = 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The finite sum of the Möbius-Mersenne terms at indices strictly below Y. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, mobiusMersenneTerm r n
/-- The rung `Θ_r = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne ladder, defined as the real sum of the atoms above. The divisor convolution `φ = μ * id` gives `Θ_2 = S - 1/2` for the binary totient series `S = ∑_{n ≥ 1} φ(n) / 2 ^ n`. At `r = 0` the family is not summable and the Lean sum takes its default value `0`; every compared theorem uses the ladder only at `r ≥ 1`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
/-- The quotient `Q(e, Y) = t_Y(e + 2) ^ 2 / t_Y(2 e + 2)` of Möbius-Mersenne prefixes, called the positive rank-one strict-subrank quotient in the surrounding development. The definition imposes neither positivity nor any admissibility condition: at `Y = 0` both prefixes are empty sums and the Lean division returns `0`. The theorems below restrict to `e ≥ 1` and `Y ≥ 4`. -/
noncomputable def rankOneSubrankQuotient (e Y : ℕ) : ℝ :=
  mobiusMersennePrefix Y (e + 2) ^ 2 /
    mobiusMersennePrefix Y (2 * e + 2)
end PalomarCorpus.E249_30.Shared

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
/-- The natural argument of an integer-intercept affine form. Its values before the form becomes nonnegative are irrelevant to an eventual relation. Local copy of ErdosProblems.Erdos249.PaperCompleteR20.integerAffineValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def integerAffineValue {ι : Type*} (a : ι → ℕ) (b : ι → ℤ)
    (i : ι) (n : ℕ) : ℕ :=
  Int.toNat ((a i : ℤ) * (n : ℤ) + b i)
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.RationalObservableClassification
open Filter Topology
open scoped BigOperators
/-- The binary-weighted sum of the least nonnegative residues φ(n) modulo m. -/
noncomputable def totientResidueValue (m : ℕ) : ℝ :=
  ∑' n : ℕ, ((Nat.totient n % m : ℕ) : ℝ) / 2 ^ n
end PalomarCorpus.E249.RationalObservableClassification

namespace PalomarCorpus.E249.PaperStatementsM
open scoped BigOperators
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249.PaperStatementsM

namespace PalomarCorpus.E249.PaperStatementsBG
open scoped BigOperators
open Matrix
open ArithmeticFunction
export PalomarCorpus.E249_30.Shared (mobiusMersennePrefix mobiusMersenneTerm mobiusMersenneTheta rankOneSubrankQuotient)
end PalomarCorpus.E249.PaperStatementsBG

namespace PalomarCorpus.E249.RankOneDenominator
open Filter Topology
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249_30.Shared (mobiusMersennePrefix mobiusMersenneTerm)
end PalomarCorpus.E249.RankOneDenominator

namespace PalomarCorpus.E249.RankOneSharpFloor
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249_30.Shared (mobiusMersennePrefix mobiusMersenneTerm mobiusMersenneTheta rankOneSubrankQuotient)
end PalomarCorpus.E249.RankOneSharpFloor
