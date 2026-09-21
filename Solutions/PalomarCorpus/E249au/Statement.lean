/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249au

Every non-theorem declaration of `PalomarCorpus/E249au/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`. Every primitive period `h₀ ≤ t` divides it. Local copy of Erdos249257.TotientTailPeriodKiller.periodLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- A one-sided actual-word gap which excludes the positive top-edge carry. Unlike total staircase annihilation, this condition merely asks the final `m`-bit residue to lie at or below the complement of the directed carry strip. By `windowDiscrepancy_emod_two_pow_eq_terminal`, it is a condition on the last `m` actual arithmetic letters alone. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.ActualLcmTopEdgeResidueGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ActualLcmTopEdgeResidueGap (a J K m : ℕ) : Prop :=
  m ≤ K ∧
    ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
      windowDiscrepancy (periodLcm (2 ^ a))
          (periodLcm (2 ^ a) + J) K % (2 : ℤ) ^ m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + J + K + 2 : ℕ) : ℤ)
/-- Cofinal supply target for the genuinely non-vacuous one-sided actual-word gap. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmTopEdgeResidueGapSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoActualLcmTopEdgeResidueGapSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m
/-- The LCM height used by the power-two endpoint at exponent `a`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The actual LCM-diagonal tail orbit at exponent `a`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)
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
/-- Predicate for a real quantity to be an integer. Local copy of Erdos249257.DiagonalPincerDecomposition.IsIntegralValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsIntegralValue (x : ℝ) : Prop := x ∈ Set.range ((↑) : ℤ → ℝ)
/-- The diagonal tail difference `D(H) = R_(2H) - R_H`. Local copy of Erdos249257.PrimeJumpWindow.diagonalTailDifferenceAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalTailDifferenceAt (H : ℕ) : ℝ :=
  totientTail (2 * H) - totientTail H
/-- Exact direct tail radius for the four-vertex commutator. Local copy of Erdos249257.PrimeJumpWindow.primeJumpSharpRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeJumpSharpRadius (H p L : ℕ) : ℤ :=
  3 * p * H + (p + 1) * (L + 2)
/-- The depth-`L` window numerator `P_L(M) = Σ_{j<L} φ(M+1+j)·2^{L-1-j}`: the integer layer of `2^L·R_M`, exact up to the one-sided deep tail `0 ≤ 2^L·R_M - P_L(M) ≤ M+L+2`. Local copy of Erdos249257.TotientTailPeriodKiller.windowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)
/-- Integer depth-`L` numerator of the four-vertex commutator, with vertices ordered as `H, 2H, pH, 2pH`. Local copy of Erdos249257.PrimeJumpWindow.primeJumpWindowCommutator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeJumpWindowCommutator (H p L : ℕ) : ℤ :=
  (windowNumerator (2 * p * H) L : ℤ) -
    (windowNumerator (p * H) L : ℤ) -
    p * (windowNumerator (2 * H) L : ℤ) +
    p * (windowNumerator H L : ℤ)
/-- Decidable direct consumer: the four-vertex window stays outside the sharp tail band around the integer lattice. Local copy of Erdos249257.PrimeJumpWindow.primeJumpSharpKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeJumpSharpKill (H p L : ℕ) : Prop :=
  primeJumpSharpRadius H p L <
      primeJumpWindowCommutator H p L % 2 ^ L ∧
    primeJumpWindowCommutator H p L % 2 ^ L <
      2 ^ L - primeJumpSharpRadius H p L
/-- The prime-jump commutator `J(H,p) = D(pH) - p D(H)`. Local copy of Erdos249257.PrimeJumpWindow.primeJumpTailCommutator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeJumpTailCommutator (H p : ℕ) : ℝ :=
  diagonalTailDifferenceAt (p * H) - p * diagonalTailDifferenceAt H
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
/-- Fixed-shift fibre-free counted window-phase anti-concentration. The sample `T` may be any nonempty subset of a cofinal dyadic block. Local copy of Erdos249257.TotientTailPeriodKiller.DTWWindowSeparatedPairsAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DTWWindowSeparatedPairsAt (h : ℕ) : Prop :=
  ∀ X₀ : ℕ, ∃ X L : ℕ, ∃ T : Finset ℕ,
      ∃ P : Finset (ℕ × ℕ), ∃ δ : ℝ,
      max X₀ 1 ≤ X ∧
      T.Nonempty ∧
      T ⊆ Finset.Ico X (2 * X) ∧
      16 * (2 * X + h + L + 2) ≤ 2 ^ L ∧
      P ⊆ T.product T ∧
      0 ≤ δ ∧
      (∀ p ∈ P,
        δ ≤ ‖windowFirstExp h p.1 L - windowFirstExp h p.2 L‖) ∧
      2 * (T.card : ℝ) ^ 2 / 5 ≤ (P.card : ℝ) * δ ^ 2
/-- Fibre-free counted window-phase anti-concentration at every positive shift; neither primality nor a pivot factorization is part of the statement. Local copy of Erdos249257.TotientTailPeriodKiller.DTWWindowSeparatedPairs, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def DTWWindowSeparatedPairs : Prop :=
  ∀ h : ℕ, 0 < h → DTWWindowSeparatedPairsAt h
/-- The integer carry orbit launched from candidate `d` at position `N`: `orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`. If `D_h(N)` is the integer `d`, this orbit equals `D_h(N+i)` forever. Local copy of Erdos249257.TotientTailPeriodKiller.carryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- Second-difference window discrepancy `A₂ = A(h, N+h, L) - A(h, N, L)`: the depth-`L` truncation of `2^L·((R_{N+2h} - R_{N+h}) - (R_{N+h} - R_N))`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy2, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy2 (h N L : ℕ) : ℤ :=
  windowDiscrepancy h (N + h) L - windowDiscrepancy h N L
/-- The decidable rank-2 certificate: the residue of `A₂` modulo `2^L` avoids the radius-`2(N+2h+L+2)` neighbourhood of `0`. The doubled radius pays for two window truncations; in exchange the second difference cancels the whole `H·C` clean shadow on the lcm cone. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedRank2Kill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedRank2Kill (h N L : ℕ) : Prop :=
  (2 * ((N : ℤ) + 2 * h + L + 2)) < windowDiscrepancy2 h N L % 2 ^ L ∧
    windowDiscrepancy2 h N L % 2 ^ L < 2 ^ L - 2 * ((N : ℤ) + 2 * h + L + 2)
/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
/-- Real part of the first additive character of the endpoint discrepancy modulo `2^L`. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstCos, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))
/-- **The supply normal form.** For every ray `d ≥ 1` and every basepoint threshold `c`, some multiple period `t·d` admits a certified kill at some `N ≥ c`. The odd part of a hypothetical denominator selects the ray; the kill contradicts the tail-period law on it. Local copy of ErdosProblems.Erdos249.PeriodMultipleEscape.PeriodMultipleKillSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PeriodMultipleKillSupply : Prop :=
  ∀ d : ℕ, 0 < d → ∀ c : ℕ,
    ∃ t N L : ℕ, 0 < t ∧ c ≤ N ∧ certifiedKill (t * d) N L
end PalomarCorpus.E249.PaperStatementsAU
