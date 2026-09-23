/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_07

Every non-theorem declaration of `PalomarCorpus/E249_07/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open Filter
open Topology
open Classical
open Module
open Matrix
open ArithmeticFunction
open scoped BigOperators

namespace PalomarCorpus.E249_07.Shared
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
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
end PalomarCorpus.E249_07.Shared

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
export PalomarCorpus.E249_07.Shared (certifiedKill totientTail windowDiscrepancy)
end PalomarCorpus.E249.PaperStatementsAD

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_07.Shared (certifiedKill totientTail windowDiscrepancy)
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

namespace PalomarCorpus.E249.PaperStructuresP
open Module
open Matrix
/-- A square nonzero evaluation minor. This is the exact finite object needed to turn number-theoretic row construction into linear independence. Local copy of Erdos249257.SeparatedMinorCertificate, restated so the compared statements elaborate against Mathlib alone. -/
structure SeparatedMinorCertificate {ι : Type*} [Fintype ι] [DecidableEq ι]
    (family : ι → ℕ → ℚ) where
  rowIndex : ι → ℕ
  det_ne_zero :
    Matrix.det (fun i j : ι => family j (rowIndex i)) ≠ 0
end PalomarCorpus.E249.PaperStructuresP

namespace PalomarCorpus.E249.PaperStatementsAP
open ArithmeticFunction
end PalomarCorpus.E249.PaperStatementsAP

namespace PalomarCorpus.E249.PaperStatementsH
open scoped BigOperators
end PalomarCorpus.E249.PaperStatementsH

namespace PalomarCorpus.E249.PaperStatementsAE
open scoped BigOperators
end PalomarCorpus.E249.PaperStatementsAE

namespace PalomarCorpus.E249.PaperStatementsAK
end PalomarCorpus.E249.PaperStatementsAK
