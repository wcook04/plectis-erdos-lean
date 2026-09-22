/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249i

Every non-theorem declaration of `PalomarCorpus/E249i/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset

namespace PalomarCorpus.E249.PaperStatementsI
open Finset
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerCertificateScales, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerCertificateScales : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17]
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerCertificateScalesThroughT64, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerCertificateScalesThroughT64 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64]
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerKillDepth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerKillDepth : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 7 => 14
  | 8 => 15
  | 9 => 14
  | 11 => 21
  | 13 => 22
  | 16 => 23
  | 17 => 26
  | _ => 0
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerKillDepthThroughT64, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerKillDepthThroughT64 : ℕ → ℕ
  | 1 => 6
  | 2 => 5
  | 3 => 7
  | 4 => 7
  | 5 => 9
  | 7 => 14
  | 8 => 15
  | 9 => 14
  | 11 => 21
  | 13 => 22
  | 16 => 23
  | 17 => 26
  | 19 => 32
  | 23 => 35
  | 25 => 38
  | 27 => 40
  | 29 => 45
  | 31 => 49
  | 32 => 50
  | 37 => 56
  | 41 => 61
  | 43 => 66
  | 47 => 73
  | 49 => 76
  | 53 => 81
  | 59 => 88
  | 61 => 94
  | 64 => 93
  | _ => 0
/-- The depth-`L` cleared binary prefix, accumulated from left to right. Equivalently this is `∑ j < L, a (n+j) * 2^(L-1-j)`. Local copy of Erdos249257.TotientTailPeriodKiller.dyadicClearedPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dyadicClearedPrefix (a : ℕ → ℤ) (n : ℕ) : ℕ → ℤ
  | 0 => 0
  | L + 1 => 2 * dyadicClearedPrefix a n L + a (n + L)
/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`. Every primitive period `h₀ ≤ t` divides it. Local copy of Erdos249257.TotientTailPeriodKiller.periodLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- State anchors corresponding to the exact whole-ray letters at `q * periodLcm t`, for `2 ≤ q < t`. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorStates, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorStates (t : ℕ) : Finset ℕ :=
  (Finset.Ico 2 t).image (fun q => (q - 1) * periodLcm t)
/-- A state which is `-A` on a finite anchor set and zero elsewhere. Local copy of Erdos249257.TotientTailPeriodKiller.sparsePulseState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sparsePulseState (A : ℤ) (S : Finset ℕ) (k : ℕ) : ℤ :=
  if k ∈ S then -A else 0
/-- The zero-based forcing letter determined by `c_{i+1} = 2c_i - a_i`. Local copy of Erdos249257.TotientTailPeriodKiller.sparsePulseLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sparsePulseLetter (A : ℤ) (S : Finset ℕ) (i : ℕ) : ℤ :=
  2 * sparsePulseState A S i - sparsePulseState A S (i + 1)
/-- The LCM pulse forcing word. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorPulseLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorPulseLetter (t i : ℕ) : ℤ :=
  sparsePulseLetter (Nat.totient (periodLcm t) : ℤ) (lcmAnchorStates t) i
/-- The LCM pulse state with amplitude `φ(periodLcm t)`. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorPulseState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorPulseState (t k : ℕ) : ℤ :=
  sparsePulseState (Nat.totient (periodLcm t) : ℤ) (lcmAnchorStates t) k
/-- Evaluation of a finite integer shift polynomial on a sequence. A term `(h, q)` contributes `q * f(n+h)`. Local copy of Erdos249257.TotientTailPeriodKiller.shiftLinearCombination, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftLinearCombination : List (ℕ × ℤ) → (ℕ → ℤ) → (ℕ → ℤ)
  | [], _ => fun _ => 0
  | (h, q) :: terms, f => fun n =>
      q * f (n + h) + shiftLinearCombination terms f n
/-- Pulse letters transformed by the same shift polynomial. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorShiftPolynomialLetter, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorShiftPolynomialLetter
    (t : ℕ) (terms : List (ℕ × ℤ)) : ℕ → ℤ :=
  shiftLinearCombination terms (lcmAnchorPulseLetter t)
/-- Pulse state transformed by an arbitrary finite integer shift polynomial. Local copy of Erdos249257.TotientTailPeriodKiller.lcmAnchorShiftPolynomialState, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmAnchorShiftPolynomialState
    (t : ℕ) (terms : List (ℕ × ℤ)) : ℕ → ℤ :=
  shiftLinearCombination terms (lcmAnchorPulseState t)
/-- The `ℓ1` weight of a finite shift polynomial. Local copy of Erdos249257.TotientTailPeriodKiller.shiftLinearWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def shiftLinearWeight : List (ℕ × ℤ) → ℤ
  | [] => 0
  | (_, q) :: terms => |q| + shiftLinearWeight terms
end PalomarCorpus.E249.PaperStatementsI
