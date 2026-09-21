/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249ax

Every non-theorem declaration of `PalomarCorpus/E249ax/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open scoped BigOperators
open Finset

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
open Finset
/-- `periodLcm t = lcm(1, …, t)`: the universal period at scale `t`. Every primitive period `h₀ ≤ t` divides it. Local copy of Erdos249257.TotientTailPeriodKiller.periodLcm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The canonical adjacent-suffix depth: ten guard bits beyond the binary scale of the LCM height. At this depth the analytic width budget is automatic; the only remaining arithmetic input is centrality of the adjacent residue. Local copy of Erdos249257.DiagonalFreshLossBridge.canonicalAdjacentSuffixDepth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  Nat.log2 (periodLcm t) + 10
/-- Make the canonical adjacent-suffix depth odd by spending at most one additional guard bit. Local copy of Erdos249257.DiagonalFreshLossBridge.oddGuardedCanonicalAdjacentSuffixDepth, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def oddGuardedCanonicalAdjacentSuffixDepth (t : ℕ) : ℕ :=
  let m := canonicalAdjacentSuffixDepth t
  if Even m then m + 1 else m
/-- The signed diagonal window increment `φ(2·H_t+s) − φ(H_t+s)` at offset `s`. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalWindowIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalWindowIncrement (t s : ℕ) : ℤ :=
  (Nat.totient (2 * periodLcm t + s) : ℤ) -
    (Nat.totient (periodLcm t + s) : ℤ)
/-- Unreduced integer block underlying the adjacent suffix displacement. It is the exact target-specific scalar evaluated by the canonical jump probe. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalAdjacentSuffixRawBlock, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalAdjacentSuffixRawBlock (t J m : ℕ) : ℤ :=
  (∑ r ∈ Finset.range m,
      diagonalWindowIncrement t (J + 1 + r) * 2 ^ (m - 1 - r)) +
    diagonalWindowIncrement t (J + m + 1)
/-- Canonical centered representative, with the positive midpoint selected in the tie case. Local copy of Erdos249257.DiagonalFreshLossBridge.actualCenteredLift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualCenteredLift (A M : ℤ) : ℤ :=
  let r := A % M
  if r ≤ M / 2 then r else r - M
/-- Actual centered half-state at power-two odd rank `q`. Local copy of Erdos249257.DiagonalFreshLossBridge.actualOddHalfCenteredLift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualOddHalfCenteredLift (a q : ℕ) : ℤ :=
  actualCenteredLift
    (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) / 2)
    ((4 : ℤ) ^ q)
/-- Cofinal actual-state form of the exact top-edge half-word producer. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualFinalTopEdgeMagnitudeSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoActualFinalTopEdgeMagnitudeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      |actualOddHalfCenteredLift a q|
/-- Cofinal one-sided producer exposed by the exact terminal/carry identity. Unlike the two-sided magnitude target, it only asks the centered state to dominate half of the final literal arithmetic letter. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoFlexibleActualTerminalDominanceSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoFlexibleActualTerminalDominanceSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q
/-- Strictly weaker cofinal producer: the witness may use any odd rank whose exact top-edge threshold fits the half-cell and whose adjacent depth remains inside the actual-LCM sign corridor. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoFlexibleActualTopEdgeMagnitudeSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoFlexibleActualTopEdgeMagnitudeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      |actualOddHalfCenteredLift a q|
/-- The exact inherited contribution at a reduced offset across a power-of-two LCM jump. Even reduced offsets double; odd reduced offsets are copied unchanged. Local copy of Erdos249257.DiagonalFreshLossBridge.powerTwoInheritedIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def powerTwoInheritedIncrement (a r : ℕ) : ℤ :=
  if Even r then
    2 * diagonalWindowIncrement (2 ^ a - 1) r
  else
    diagonalWindowIncrement (2 ^ a - 1) r
/-- The odd post-jump offset not reconstructed by the even-offset seam. The name records its role in the cocycle, not an arithmetic independence claim. Local copy of Erdos249257.DiagonalFreshLossBridge.powerTwoFreshOddIncrement, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def powerTwoFreshOddIncrement (a q : ℕ) : ℤ :=
  diagonalWindowIncrement (2 ^ a) (2 * q + 1)
/-- The signed correction in one odd-depth/base-four power-of-two step. Local copy of Erdos249257.DiagonalFreshLossBridge.powerTwoOddDepthCorrection, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def powerTwoOddDepthCorrection (a n : ℕ) : ℤ :=
  powerTwoFreshOddIncrement a (n + 1) -
    2 * powerTwoInheritedIncrement a (n + 1) +
    powerTwoInheritedIncrement a (n + 2)
/-- The integral half-correction cocycle. Local copy of Erdos249257.DiagonalFreshLossBridge.powerTwoOddHalfCorrectionWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def powerTwoOddHalfCorrectionWord (a : ℕ) : ℕ → ℤ
  | 0 => 0
  | q + 1 =>
      4 * powerTwoOddHalfCorrectionWord a q +
        powerTwoOddDepthCorrection a q / 2
/-- Odd-depth half-word form of the one-sided top-edge producer. If `m = 2q+1`, the adjacent suffix residue is twice the half-word residue, and both directed edge widths divide by two to the same exact threshold `periodLcm (2^a) + q + 2`. This is substantially weaker than the older fixed `1/32` central band. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoOddGuardTopEdgeHalfWordBandSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoOddGuardTopEdgeHalfWordBandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
      powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
    powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
      (4 : ℤ) ^ q -
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ)
/-- The depth-`L` window numerator `P_L(M) = Σ_{j<L} φ(M+1+j)·2^{L-1-j}`: the integer layer of `2^L·R_M`, exact up to the one-sided deep tail `0 ≤ 2^L·R_M - P_L(M) ≤ M+L+2`. Local copy of Erdos249257.TotientTailPeriodKiller.windowNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowNumerator (M L : ℕ) : ℕ :=
  ∑ j ∈ Finset.range L, Nat.totient (M + 1 + j) * 2 ^ (L - 1 - j)
/-- The depth-`m` binary residue of the diagonal window suffix that starts after the cut `J`: the last `m` bits of the depth-`(J + m)` diagonal window, computed from the translated windows alone. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalSuffixResidue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalSuffixResidue (t J m : ℕ) : ℤ :=
  ((windowNumerator (2 * periodLcm t + J) m : ℤ) -
    (windowNumerator (periodLcm t + J) m : ℤ)) % 2 ^ m
/-- The canonical modular displacement from the suffix at cut `J` to the suffix at cut `J + 1`. Local copy of Erdos249257.DiagonalFreshLossBridge.diagonalAdjacentSuffixResidue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def diagonalAdjacentSuffixResidue (t J m : ℕ) : ℤ :=
  (diagonalSuffixResidue t (J + 1) m -
    diagonalSuffixResidue t J m) % 2 ^ m
/-- The window discrepancy `A_{h,N,L} = ∑_{j=0}^{L-1} (φ(N+h+1+j) - φ(N+1+j))·2^{L-1-j}`: the depth-`L` truncation of `2^L·(R_{N+h} - R_N)`. Local copy of Erdos249257.TotientTailPeriodKiller.windowDiscrepancy, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The integer window obtained from the three cone differences based at `H`. Local copy of Erdos249257.JointExponentTransport.joint35ConeWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def joint35ConeWindow (H L : ℕ) : ℤ :=
  windowDiscrepancy (14 * H) H L -
    3 * windowDiscrepancy (2 * H) H L -
    2 * windowDiscrepancy (4 * H) H L
/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The residue angle used by the first additive character. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstAngle, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstAngle (h N L : ℕ) : ℝ :=
  2 * Real.pi *
    (((windowDiscrepancy h N L % (2 ^ L : ℤ) : ℤ) : ℝ) /
      ((2 ^ L : ℤ) : ℝ))
/-- The complex first additive character of the endpoint discrepancy. Local copy of Erdos249257.TotientTailPeriodKiller.windowFirstExp, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def windowFirstExp (h N L : ℕ) : ℂ :=
  Complex.exp ((windowFirstAngle h N L : ℂ) * Complex.I)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperGridNumerator (H L q : ℕ) : ℕ :=
  ∑ j ∈ Finset.Icc 1 L, Nat.totient (q * H + j) * 2 ^ (L - j)
/-- Local copy of ErdosProblems.Erdos249.PaperCompleteR20.paperGridCertificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def paperGridCertificate (H L : ℕ) (Q : Finset ℕ) : Prop :=
  ∀ qi ∈ Q, ∃ qj ∈ Q,
    (qj * H + L + 2 : ℤ) <
      ((paperGridNumerator H L qi : ℤ) - paperGridNumerator H L qj) % 2 ^ L
/-- **Item 1 of `prop:te-chain`, exactly as displayed.** The two-sided band on the adjacent-suffix residue at one candidate depth `m`, with the paper's upper endpoint `2^m - (2H + m + 2)`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.PaperAdjacentSuffixMidbandSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PaperAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)
end PalomarCorpus.E249.PaperStatementsAX
