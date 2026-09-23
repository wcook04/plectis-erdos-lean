/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_06

Every non-theorem declaration of `PalomarCorpus/E249_06/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Matrix
open ArithmeticFunction
open Finset
open Filter
open Topology
open Classical

namespace PalomarCorpus.E249_06.Shared
/-- Local copy of Erdos249257.TotientTailPeriodKiller.diagonalPincerCertificateScalesThroughT64, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalPincerCertificateScalesThroughT64 : List ℕ := [1, 2, 3, 4, 5, 7, 8, 9, 11, 13, 16, 17, 19, 23, 25, 27, 29, 31, 32, 37, 41, 43, 47, 49, 53, 59, 61, 64]
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
end PalomarCorpus.E249_06.Shared

namespace PalomarCorpus.E249.PaperStatementsAF
open scoped BigOperators
open Matrix
open ArithmeticFunction
end PalomarCorpus.E249.PaperStatementsAF

namespace PalomarCorpus.E249.PaperStatementsG
export PalomarCorpus.E249_06.Shared (diagonalPincerCertificateScalesThroughT64 diagonalPincerKillDepthThroughT64)
/-- The arguments of the totient evaluations in a family of two windows. Local copy of ErdosProblems.Erdos249.PaperCompleteR20.certificateWindowIndices, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certificateWindowIndices (H N L : ℕ) : Finset ℕ :=
  (Finset.Icc 1 H).biUnion fun h =>
    (Finset.range L).image (fun j => N + 1 + j) ∪
      (Finset.range L).image (fun j => N + h + 1 + j)
end PalomarCorpus.E249.PaperStatementsG

namespace PalomarCorpus.E249.PaperStatementsI
open Finset
export PalomarCorpus.E249_06.Shared (certifiedKill diagonalPincerCertificateScalesThroughT64 diagonalPincerKillDepthThroughT64 windowDiscrepancy)
/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`. Every primitive period `h₀ ≤ t` divides it. Local copy of Erdos249257.TotientTailPeriodKiller.periodLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
end PalomarCorpus.E249.PaperStatementsI

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
export PalomarCorpus.E249_06.Shared (certifiedKill totientTail windowDiscrepancy)
end PalomarCorpus.E249.PaperStatementsAD

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_06.Shared (certifiedKill totientTail windowDiscrepancy)
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAI
open Filter
open Topology
end PalomarCorpus.E249.PaperStatementsAI

namespace PalomarCorpus.E249.PaperStatementsAJ
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAL
open Classical
/-- **The paper's binary example.** Reading the expansion two digits at a time, the block with index `k ≥ 1` is `10` when `k` is a perfect square and `01` otherwise. Position `n` sits inside the block with index `n / 2 + 1`, and is that block's first digit exactly when `n` is even. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.digit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def digit (n : ℕ) : ℕ :=
  if IsSquare (n / 2 + 1) ↔ n % 2 = 0 then 1 else 0
/-- The real number whose binary digits, read from position `n` on, are `d n, d (n+1), d (n+2), …`. For `n = 0` this is the number itself; for general `n` it is the tail left after `n` binary shifts. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.tail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def tail (d : ℕ → ℕ) (n : ℕ) : ℝ := ∑' k : ℕ, (d (n + k) : ℝ) / 2 ^ (k + 1)
/-- **ξ**, the number of the paper's binary example. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.xi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def xi : ℝ := tail digit 0
end PalomarCorpus.E249.PaperStatementsAL
