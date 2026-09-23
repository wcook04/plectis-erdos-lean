/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_12

Every non-theorem declaration of `PalomarCorpus/E249_12/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open scoped BigOperators
open Filter
open Topology
open Module
open Set

namespace PalomarCorpus.E249_12.Shared
/-- Canonical centered representative, with the positive midpoint selected in the tie case. Local copy of Erdos249257.DiagonalFreshLossBridge.actualCenteredLift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualCenteredLift (A M : ℤ) : ℤ :=
  let r := A % M
  if r ≤ M / 2 then r else r - M
/-- The shifted totient difference `φ(n + h) - φ(n)`, taken in `ℤ` through the cast from `ℕ`. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The integer carry orbit launched from candidate `d` at position `N`: `orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`. If `D_h(N)` is the integer `d`, this orbit equals `D_h(N+i)` forever. Local copy of Erdos249257.TotientTailPeriodKiller.carryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)
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
end PalomarCorpus.E249_12.Shared

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_12.Shared (carryOrbit certifiedKill deltaTotient periodLcm totientTail windowDiscrepancy)
/-- The asymmetric central-arc certificate. Its low radius is only `N+L+2`, while its high wrap radius remains `N+h+L+2`. It is therefore strictly weaker, and potentially strictly more useful, than `certifiedKill` when `h>0`. Local copy of Erdos249257.directedCertifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def directedCertifiedKill (h N L : ℕ) : Prop :=
  (N + L + 2 : ℤ) ≤ windowDiscrepancy h N L % (2 : ℤ) ^ L ∧
    windowDiscrepancy h N L % (2 : ℤ) ^ L ≤
      (2 : ℤ) ^ L - (N + h + L + 2 : ℤ)
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
export PalomarCorpus.E249_12.Shared (actualCenteredLift carryOrbit deltaTotient periodLcm totientTail windowDiscrepancy)
/-- The signed diagonal window increment `φ(2·H_t+s) − φ(H_t+s)` at offset `s`. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalWindowIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalWindowIncrement (t s : ℕ) : ℤ :=
  (Nat.totient (2 * periodLcm t + s) : ℤ) -
    (Nat.totient (periodLcm t + s) : ℤ)
/-- Unreduced integer block underlying the adjacent suffix displacement. It is the exact target-specific scalar evaluated by the canonical jump probe. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalAdjacentSuffixRawBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalAdjacentSuffixRawBlock (t J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) +
    diagonalWindowIncrement t (J + m + 1)
/-- Actual centered half-state at power-two odd rank `q`. Local copy of Erdos249257.DiagonalFreshLossBridge.actualOddHalfCenteredLift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualOddHalfCenteredLift (a q : ℕ) : ℤ :=
  actualCenteredLift
    (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
    ((4 : ℤ) ^ q)
end PalomarCorpus.E249.PaperStatementsAX

namespace PalomarCorpus.E249.PaperStatementsAY
open scoped BigOperators
export PalomarCorpus.E249_12.Shared (actualCenteredLift)
end PalomarCorpus.E249.PaperStatementsAY

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_12.Shared (carryOrbit certifiedKill deltaTotient periodLcm totientTail windowDiscrepancy)
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- The exact ordering socket for the fixed-rank curvature: the rank-two totient is strictly below both outer ranks or strictly above both of them. This is the local conclusion supplied by any factor-separated ordering of the three nonproportional linear forms. The unresolved arithmetic step for Erdős #249 is to force this socket on cofinally many prescribed LCM heights, not merely on a positive-density set of unrestricted heights. Local copy of Erdos249257.TotientFixedRankLcmAsymptotic.MiddleRankTotientExtremal, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def MiddleRankTotientExtremal (H j : ℕ) : Prop :=
  (Nat.totient (2 * H + j) < Nat.totient (H + j) ∧
      Nat.totient (2 * H + j) < Nat.totient (3 * H + j)) ∨
    (Nat.totient (H + j) < Nat.totient (2 * H + j) ∧
      Nat.totient (3 * H + j) < Nat.totient (2 * H + j))
/-- The wave-17 gap certificate at window `(N, K)` for the denominator `q`: the committed totient residue avoids the thin band of width `q(N+K+2)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.GapCertificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def GapCertificate (N K q : ℕ) : Prop :=
  (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K))
      % 2 ^ K + q * (N + K + 2) < 2 ^ K
/-- `sup_K (b+d)(K) = ∞`: the proved Farey-gap denominator-exclusion bounds on the `N = 1` window family are arbitrarily large, that is, every finite denominator range `[1, Q]` is excluded by some single window `K`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.FareyGapExclusionUnbounded, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FareyGapExclusionUnbounded : Prop :=
  ∀ Q : ℕ, ∃ K : ℕ, ∀ q : ℕ, 0 < q → q ≤ Q → GapCertificate 1 K q
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsC
open Filter
open Topology
open Finset
export PalomarCorpus.E249_12.Shared (certifiedKill periodLcm windowDiscrepancy)
end PalomarCorpus.E249.PaperStatementsC

namespace PalomarCorpus.E249.PaperStatementsBH
open Module
open Filter
open Set
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The full carry-section family through levels `1,...,e`. Local copy of Erdos249257.TotientCarryIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- A dyadic section of an integer carry orbit, viewed over `ℚ`. Local copy of Erdos249257.carryKernelSeq, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)
/-- Every carry section through levels `1,...,e`, without quotienting or identifying residue channels. Local copy of Erdos249257.canonicalCarryKernelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val
end PalomarCorpus.E249.PaperStatementsBH
