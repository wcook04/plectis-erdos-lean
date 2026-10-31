/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_14

Every non-theorem declaration of `PalomarCorpus/E249_14/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open scoped BigOperators

namespace PalomarCorpus.E249_14.Shared
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
end PalomarCorpus.E249_14.Shared

namespace PalomarCorpus.E249.PaperStatementsAK
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_14.Shared (certifiedKill periodLcm windowDiscrepancy)
/-- The integral correction for the primes shared by `j` and `x` in the totient of the product `j*x`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.totientOverlapFactor, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientOverlapFactor (j x : ℕ) : ℕ :=
  (Nat.totient j / Nat.totient (Nat.gcd j x)) * Nat.gcd j x
/-- The quotient-scale letter attached to a divisor offset `j | H` on the actual diagonal. Its two overlap factors record exactly which saturated prime powers of `j` reappear in `H/j + 1` and `2*(H/j) + 1`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.lcmDivisorRayLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmDivisorRayLetter (H j : ℕ) : ℤ :=
  let a := H / j
  ((totientOverlapFactor j (2 * a + 1) *
      Nat.totient (2 * a + 1) : ℕ) : ℤ) -
    ((totientOverlapFactor j (a + 1) *
      Nat.totient (a + 1) : ℕ) : ℤ)
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- Actual LCM-ray letter: divisor offsets use the exact quotient-scale formula, while nondivisor offsets retain the literal totient difference. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.lcmRayArithmeticLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmRayArithmeticLetter (t j : ℕ) : ℤ :=
  if j ∣ periodLcm t then
    lcmDivisorRayLetter (periodLcm t) j
  else
    deltaTotient (periodLcm t) (periodLcm t + j)
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- The two scale-`b` guard bits of a `(b+2)`-bit residue are mixed. The intervals are exactly the binary cylinders `01` and `10`; every lower bit is left unrestricted. Local copy of Erdos249257.TotientTailPeriodKiller.DyadicMixedGuard, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DyadicMixedGuard (A : ℤ) (b : ℕ) : Prop :=
  let P : ℤ := (2 : ℤ) ^ b
  let r : ℤ := A % (2 : ℤ) ^ (b + 2)
  (P ≤ r ∧ r < 2 * P) ∨ (2 * P ≤ r ∧ r < 3 * P)
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_14.Shared (certifiedKill periodLcm totientTail windowDiscrepancy)
/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_14.Shared (periodLcm totientTail)
/-- The signed diagonal window increment `φ(2·H_t+s) − φ(H_t+s)` at offset `s`. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalWindowIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalWindowIncrement (t s : ℕ) : ℤ :=
  (Nat.totient (2 * periodLcm t + s) : ℤ) -
    (Nat.totient (periodLcm t + s) : ℤ)
/-- Unreduced integer block underlying the adjacent suffix displacement. It is the exact target-specific scalar evaluated by the canonical jump probe. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalAdjacentSuffixRawBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalAdjacentSuffixRawBlock (t J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) +
    diagonalWindowIncrement t (J + m + 1)
/-- The normalized unreduced raw block at odd rank `q`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawApprox, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmRawApprox (a q : ℕ) : ℝ :=
  (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)
end PalomarCorpus.E249.PaperStatementsAX
