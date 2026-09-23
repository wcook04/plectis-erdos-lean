/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_10

Every non-theorem declaration of `PalomarCorpus/E249_10/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset

namespace PalomarCorpus.E249_10.Shared
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
/-- The depth-`L` window numerator `P_L(M) = Σ_{j<L} φ(M+1+j)·2^{L-1-j}`: the integer layer of `2^L·R_M`, exact up to the one-sided deep tail `0 ≤ 2^L·R_M - P_L(M) ≤ M+L+2`. Local copy of Erdos249257.TotientTailPeriodKiller.windowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)
end PalomarCorpus.E249_10.Shared

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_10.Shared (periodLcm totientTail windowDiscrepancy windowNumerator)
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The diagonal tail difference `D(H) = R_(2H) - R_H`. Local copy of Erdos249257.PrimeJumpWindow.diagonalTailDifferenceAt, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalTailDifferenceAt (H : ℕ) : ℝ :=
  totientTail (2 * H) - totientTail H
/-- The prime-jump commutator `J(H,p) = D(pH) - p D(H)`. Local copy of Erdos249257.PrimeJumpWindow.primeJumpTailCommutator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeJumpTailCommutator (H p : ℕ) : ℝ :=
  diagonalTailDifferenceAt (p * H) - p * diagonalTailDifferenceAt H
/-- Integer depth-`L` numerator of the four-vertex commutator, with vertices ordered as `H, 2H, pH, 2pH`. Local copy of Erdos249257.PrimeJumpWindow.primeJumpWindowCommutator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def primeJumpWindowCommutator (H p L : ℕ) : ℤ :=
  (windowNumerator (2 * p * H) L : ℤ) -
    (windowNumerator (p * H) L : ℤ) -
    p * (windowNumerator (2 * H) L : ℤ) +
    p * (windowNumerator H L : ℤ)
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
/-- The integer carry orbit launched from candidate `d` at position `N`: `orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`. If `D_h(N)` is the integer `d`, this orbit equals `D_h(N+i)` forever. Local copy of Erdos249257.TotientTailPeriodKiller.carryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
/-- Real part of the first additive character of the endpoint discrepancy modulo `2^L`. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstCos, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstCos (h N L : ℕ) : ℝ :=
  Real.cos
    (2 * Real.pi *
      (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
        ((2 ^ L : ℤ) : ℝ)))
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAJ
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_10.Shared (periodLcm totientTail windowDiscrepancy windowNumerator)
end PalomarCorpus.E249.PaperStatementsAU
