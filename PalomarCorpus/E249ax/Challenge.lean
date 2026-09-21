/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band x

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open scoped BigOperators
open Finset

namespace PalomarCorpus.E249.PaperStatementsAX
open scoped BigOperators
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
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The LCM height used by the power-two endpoint at exponent `a`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)
/-- The actual LCM-diagonal tail orbit at exponent `a`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmTailOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)
/-- Cofinal non-integrality of the actual power-two LCM-diagonal tail orbit. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmOrbitNonintegralitySupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoActualLcmOrbitNonintegralitySupply : Prop :=
  ∀ a₀ : ℕ, ∃ a, a₀ ≤ a ∧
    actualLcmTailOrbit a ∉ Set.range ((↑) : ℤ → ℝ)
/-- The elementary error radius for the odd-rank raw approximation. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawErrorRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmRawErrorRadius (a q : ℕ) : ℝ :=
  ((2 * actualLcmHeight a + 2 * q + 3 : ℕ) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)
/-- Cofinal quantitative anti-concentration of the actual LCM tail orbit at the canonical odd ranks. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmOrbitSeparationSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoActualLcmOrbitSeparationSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, max 2 a₀ ≤ a ∧
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
    ∀ z : ℤ,
      (1 : ℝ) / 32 + actualLcmRawErrorRadius a q ≤
        |actualLcmTailOrbit a - (z : ℝ)|
/-- Cofinal supply target for the genuinely non-vacuous one-sided actual-word gap. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoActualLcmTopEdgeResidueGapSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoActualLcmTopEdgeResidueGapSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a K m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    K + (a + 6) < 2 * 2 ^ a ∧ ActualLcmTopEdgeResidueGap a 0 K m
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
/-- The exact cofinal arithmetic socket exposed by one-sided adjacent-gap geometry. At depth `m`, the adjacent suffix displacement avoids only the two individual upper-edge arcs. The buffer is stated for the larger candidate depth `m + 1`, so either branch produced below remains inside the actual-LCM sign corridor. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoAdjacentSuffixMidbandSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoAdjacentSuffixMidbandSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    m + 1 + (a + 6) < 2 * 2 ^ a ∧
    ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
    ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
    diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
      (2 : ℤ) ^ m -
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ)
/-- Cofinal supply of odd ranks whose centered state escapes the exact open terminal/carry corridor forced by an integral actual-LCM orbit. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply : Prop :=
  ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
    2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
    2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
    (2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ) ∨
      diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
        2 * actualOddHalfCenteredLift a q)
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
/-- The normalized unreduced raw block at odd rank `q`. Local copy of Erdos249257.DiagonalFreshLossBridge.PowerTwoOddWindowAffine.actualLcmRawApprox, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def actualLcmRawApprox (a q : ℕ) : ℝ :=
  (diagonalAdjacentSuffixRawBlock (2 ^ a) 0 (2 * q + 1) : ℝ) /
    (2 : ℝ) ^ (2 * q + 1)
/-- Signed distance of the canonical adjacent residue from the nearer edge of the fixed central band. Nonnegative slack is exactly the two-sided centrality condition; this scalar is the proof-oriented cocycle to study at strict LCM jumps. Local copy of Erdos249257.DiagonalFreshLossBridge.canonicalAdjacentSuffixCentralSlack, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalAdjacentSuffixCentralSlack (t : ℕ) : ℤ :=
  let m := canonicalAdjacentSuffixDepth t
  let d := diagonalAdjacentSuffixResidue t 0 m
  min (d - 2 ^ (m - 5)) ((2 ^ m - 2 ^ (m - 5)) - d)
/-- The integer window obtained from the three cone differences based at `H`. Local copy of Erdos249257.JointExponentTransport.joint35ConeWindow, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def joint35ConeWindow (H L : ℕ) : ℤ :=
  windowDiscrepancy (14 * H) H L -
    3 * windowDiscrepancy (2 * H) H L -
    2 * windowDiscrepancy (4 * H) H L
/-- `Hₜ = lcm(1, ..., t)`. The interval avoids inserting zero into the finite LCM. Local copy of Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)
/-- The window step `a_n = φ(n+h) - φ(n)` driving the carry recurrence. Local copy of Erdos249257.TotientTailPeriodKiller.deltaTotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The integer carry orbit launched from candidate `d` at position `N`: `orbit 0 = d`, `orbit (i+1) = 2·orbit i - a_{N+i+1}`. If `D_h(N)` is the integer `d`, this orbit equals `D_h(N+i)` forever. Local copy of Erdos249257.TotientTailPeriodKiller.carryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryOrbit (h N : ℕ) (d : ℤ) : ℕ → ℤ
  | 0 => d
  | i + 1 => 2 * carryOrbit h N d i - deltaTotient h (N + i + 1)
/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
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
/-- The paper's prescribed index `q_a = ⌊(⌊log₂ H⌋ + 10)/2⌋`, so that `2q_a + 1` is the least odd integer at least `⌊log₂ H⌋ + 10`. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.prescribedOddIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def prescribedOddIndex (a : ℕ) : ℕ := (Nat.log2 (periodLcm (2 ^ a)) + 10) / 2
/-- States catalogue:cert:b10a, prop:B10 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_nonintegral_pair in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_grid_nonintegral_pair (H L : ℕ) (Q : Finset ℕ) (hQ : Q.Nonempty)
    (hfloor : ∀ q ∈ Q, (q * H + L + 2 : ℤ) < 2 ^ L)
    (hcert : paperGridCertificate H L Q) :
    ∃ qi ∈ Q, ∃ qj ∈ Q,
      totientTail (qj * H) - totientTail (qi * H) ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:cert:b10b, prop:B10 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_grid_supply_irrational in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finite_grid_supply_irrational
    (hs : ∀ t₀ : ℕ, ∃ t, t₀ ≤ t ∧ ∃ L : ℕ, ∃ Q : Finset ℕ,
      Q.Nonempty ∧ (∀ q ∈ Q, 0 < q) ∧
      (∀ q ∈ Q, (q * periodLcm t + L + 2 : ℤ) < 2 ^ L) ∧
      paperGridCertificate (periodLcm t) L Q) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:cert:b10a, catalogue:cert:b10b, prop:B10 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.paperGridNumerator_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperGridNumerator_eq (H L q : ℕ) :
    paperGridNumerator H L q = windowNumerator (q * H) L := by
  sorry
/-- States catalogue:cert:a9 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR20.specified_euler_tail_period in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem specified_euler_tail_period
    (a : ℤ) (c v : ℕ) (hv : 0 < v) (hodd : Odd v)
    (hS : (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      (a : ℝ) / ((2 : ℝ) ^ c * (v : ℝ))) :
    0 < Nat.totient v ∧ ∀ N : ℕ, c ≤ N →
      totientTail (N + Nat.totient v) - totientTail N ∈
        Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:SEP-02-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_explicit (a q : ℕ) : := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_actualLcmTailOrbit_sub_rawApprox_lt_paper_form (a q : ℕ) : := by
  sorry
/-- States prop:SEP-03 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_orbit_sub_rawApprox_lt in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_orbit_sub_rawApprox_lt (a q : ℕ) : := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.actualLcmRawApprox_isRat in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem actualLcmRawApprox_isRat (a q : ℕ) :
    ∃ v : ℚ, actualLcmRawApprox a q = (v : ℝ) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.canonicalAdjacentSuffixCentralSlack_paper_formula in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonicalAdjacentSuffixCentralSlack_paper_formula (t : ℕ) :
    canonicalAdjacentSuffixCentralSlack t =
      min ((windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                (Nat.log2 (periodLcm t) + 10)
              - windowDiscrepancy (periodLcm t) (periodLcm t)
                (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10)
          - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5))
        (2 ^ (Nat.log2 (periodLcm t) + 10)
            - 2 ^ (Nat.log2 (periodLcm t) + 10 - 5)
          - (windowDiscrepancy (periodLcm t) (periodLcm t + 1)
                 (Nat.log2 (periodLcm t) + 10)
               - windowDiscrepancy (periodLcm t) (periodLcm t)
                 (Nat.log2 (periodLcm t) + 10))
            % 2 ^ (Nat.log2 (periodLcm t) + 10)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.corridor_escape_and_irrational_of_magnitude in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem corridor_escape_and_irrational_of_magnitude :
    (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by
  sorry
/-- States prop:TE-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.endpoint_criterion_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem endpoint_criterion_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hesc : 2 * actualOddHalfCenteredLift a q ≤
          diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
            ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℤ) ∨
        diagonalWindowIncrement (2 ^ a) (2 * q + 2) ≤
          2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a)) ∉
      Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:TE-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.endpoint_identity in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem endpoint_identity {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 2 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    {z : ℤ}
    (hz : (z : ℝ) = totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))) :
    2 * actualOddHalfCenteredLift a q =
      diagonalWindowIncrement (2 ^ a) (2 * q + 2) -
        carryOrbit (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) z (2 * q + 1) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_actualLcmOrbitSeparationSupply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_actualLcmOrbitSeparationSupply
    (hsupply : PowerTwoActualLcmOrbitSeparationSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_lower_escape_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_lower_escape_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
      2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
      2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
      2 * actualOddHalfCenteredLift a q ≤
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) -
          ((2 * periodLcm (2 ^ a) + (2 * q + 1) + 2 : ℕ) : ℤ)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_paperAdjacentSuffixMidbandSupply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_paperAdjacentSuffixMidbandSupply
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_powerTwo_postJump_slack_supply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_powerTwo_postJump_slack_supply
    (hsupply : ∀ a₀ : ℕ, ∃ a, max 2 a₀ ≤ a ∧
      0 ≤ canonicalAdjacentSuffixCentralSlack (2 ^ a)) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_terminalDominanceSupply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_terminalDominanceSupply
    (hsupply : PowerTwoFlexibleActualTerminalDominanceSupply) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35ConeWindow_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35ConeWindow_eq (H L : ℕ) :
    joint35ConeWindow H L
      = ∑ j ∈ Finset.range L,
          ((Nat.totient (15 * H + (j + 1)) : ℤ)
            - 3 * (Nat.totient (3 * H + (j + 1)) : ℤ)
            - 2 * (Nat.totient (5 * H + (j + 1)) : ℤ)
            + 4 * (Nat.totient (H + (j + 1)) : ℤ)) * 2 ^ (L - (j + 1)) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_nonintegral_of_separated_window in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_nonintegral_of_separated_window {H L : ℕ} (hH : 1 ≤ H)
    (hlow : ((19 * H + 5 * L + 5 : ℕ) : ℤ) < joint35ConeWindow H L % 2 ^ L)
    (hhigh : joint35ConeWindow H L % 2 ^ L
      < 2 ^ L - ((19 * H + 5 * L + 5 : ℕ) : ℤ)) :
    (totientTail (15 * H) - 3 * totientTail (3 * H)
      - 2 * totientTail (5 * H) + 4 * totientTail H) ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.joint35_truncation_error in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_truncation_error (H L : ℕ) (hH : 1 ≤ H) :
    (2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)
      = (totientTail (15 * H + L) + 4 * totientTail (H + L))
        - (3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L))
    ∧ |(2 : ℝ) ^ L * (totientTail (15 * H) - 3 * totientTail (3 * H)
        - 2 * totientTail (5 * H) + 4 * totientTail H)
        - (joint35ConeWindow H L : ℝ)|
      ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)
    ∧ (0 ≤ totientTail (15 * H + L) + 4 * totientTail (H + L)
        ∧ totientTail (15 * H + L) + 4 * totientTail (H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ))
    ∧ (0 ≤ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
        ∧ 3 * totientTail (3 * H + L) + 2 * totientTail (5 * H + L)
          ≤ ((19 * H + 5 * L + 5 : ℕ) : ℝ)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.lcmHeight_eq_periodLcm in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem lcmHeight_eq_periodLcm (t : ℕ) : lcmHeight t = periodLcm t := by
  sorry
/-- States prop:SEP-03 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.oddGuarded_depth_eq_prescribed in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem oddGuarded_depth_eq_prescribed (a : ℕ) :
    oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * prescribedOddIndex a + 1 := by
  sorry
/-- States prop:TE-06 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.oddHalfCenteredLift_spec in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem oddHalfCenteredLift_spec {a : ℕ} (q : ℕ) (ha : 2 ≤ a) :
    Even (windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
        diagonalWindowIncrement (2 ^ a) (2 * q + 2)) ∧
      Int.ModEq ((4 : ℤ) ^ q) (actualOddHalfCenteredLift a q)
        ((windowDiscrepancy (periodLcm (2 ^ a)) (periodLcm (2 ^ a)) (2 * q + 1) +
          diagonalWindowIncrement (2 ^ a) (2 * q + 2)) / 2) ∧
      -((4 : ℤ) ^ q) < 2 * actualOddHalfCenteredLift a q ∧
      2 * actualOddHalfCenteredLift a q ≤ (4 : ℤ) ^ q := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperAdjacentSuffixMidbandSupply_of_adjacentSuffixMidband
    (hsupply : PowerTwoAdjacentSuffixMidbandSupply) :
    PaperAdjacentSuffixMidbandSupply := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperAdjacentSuffixMidbandSupply_of_flexibleActualTopEdgeMagnitude
    (hsupply : PowerTwoFlexibleActualTopEdgeMagnitudeSupply) :
    PaperAdjacentSuffixMidbandSupply := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperAdjacentSuffixMidbandSupply_of_oddGuardTopEdgeHalfWordBand
    (hsupply : PowerTwoOddGuardTopEdgeHalfWordBandSupply) :
    PaperAdjacentSuffixMidbandSupply := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_fifth_gives_nonintegrality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_fifth_gives_nonintegrality :
    PowerTwoFlexibleActualTerminalDominanceSupply →
      PowerTwoActualLcmOrbitNonintegralitySupply := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_first_four_imply_topEdgeSupply in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_first_four_imply_topEdgeSupply :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_five_sufficient_for_irrationality in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_five_sufficient_for_irrationality :
    (PaperAdjacentSuffixMidbandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_item_one_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_item_one_unfolded :
    PaperAdjacentSuffixMidbandSupply ↔
      ∀ a₀ : ℕ, ∃ a m : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        m + 1 + (a + 6) < 2 * 2 ^ a ∧
        ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m ∧
        ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
          diagonalAdjacentSuffixResidue (2 ^ a) 0 m ∧
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
          (2 : ℤ) ^ m - ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.paperTeChain_relations in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paperTeChain_relations :
    (PaperAdjacentSuffixMidbandSupply → PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PaperAdjacentSuffixMidbandSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem powerTwoActualLcmTopEdgeResidueGapSupply_of_paperAdjacentSuffixMidband
    (hsupply : PaperAdjacentSuffixMidbandSupply) :
    PowerTwoActualLcmTopEdgeResidueGapSupply := by
  sorry
/-- States prop:SEP-03 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.rawApprox_separation_of_orbit_separation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rawApprox_separation_of_orbit_separation {a q : ℕ}
    (hsep : ∀ z : ℤ,
      (1 : ℝ) / 32 + ((2 * periodLcm (2 ^ a) + 2 * q + 3 : ℕ) : ℝ) / (2 : ℝ) ^ (2 * q + 1) ≤ := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_sq_dist_from_phase_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sum_sq_dist_from_phase_one (h L : ℕ) (T : Finset ℕ) :
    ∑ N ∈ T, ‖windowFirstExp h N L - 1‖ ^ 2 =
      2 * (T.card : ℝ) - 2 * ∑ N ∈ T, (windowFirstExp h N L).re := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_eq_coefficient_mul_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailDifference_eq_coefficient_mul_series (H : ℕ) :
    totientTail (2 * H) - totientTail H =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
          (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) +
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ)) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tailDifference_sub_rationalApproximation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tailDifference_sub_rationalApproximation (H D : ℕ) :
    totientTail (2 * H) - totientTail H -
        (((totientPrefix H : ℕ) : ℝ) - ((totientPrefix (2 * H) : ℕ) : ℝ) +
          (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
            (1 / 2 +
              ∑ d ∈ Finset.Icc 1 D,
                ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
                  (((2 : ℝ) ^ d - 1) ^ 2))) =
      (2 : ℝ) ^ H * ((2 : ℝ) ^ H - 1) *
        ∑' k : ℕ,
          ((ArithmeticFunction.moebius (D + 1 + k) : ℤ) : ℝ) /
            (((2 : ℝ) ^ (D + 1 + k) - 1) ^ 2) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_five_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem teChain_item_five_unfolded :
    PowerTwoFlexibleActualTerminalDominanceSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
          2 * actualOddHalfCenteredLift a q := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_four_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem teChain_item_four_unfolded :
    PowerTwoFlexibleActualTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, a₀ ≤ a ∧ 8 ≤ a ∧
        2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a ∧
        2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_three_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem teChain_item_three_unfolded :
    PowerTwoActualFinalTopEdgeMagnitudeSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ |actualOddHalfCenteredLift a q| := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.teChain_item_two_unfolded in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem teChain_item_two_unfolded :
    PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
      ∀ a₀ : ℕ, ∃ a q : ℕ, max 14 a₀ ≤ a ∧
        oddGuardedCanonicalAdjacentSuffixDepth (2 ^ a) = 2 * q + 1 ∧
        ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤
          powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ∧
        powerTwoOddHalfCorrectionWord a q % (4 : ℤ) ^ q ≤
          (4 : ℤ) ^ q - ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) := by
  sorry
/-- States prop:TE-05 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.te_chain_relations in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem te_chain_relations :
    (PowerTwoOddGuardTopEdgeHalfWordBandSupply ↔
        PowerTwoActualFinalTopEdgeMagnitudeSupply) ∧
      (PowerTwoActualFinalTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTopEdgeMagnitudeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoAdjacentSuffixMidbandSupply) ∧
      (PowerTwoAdjacentSuffixMidbandSupply →
        PowerTwoActualLcmTopEdgeResidueGapSupply) ∧
      (PowerTwoFlexibleActualTerminalDominanceSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTopEdgeMagnitudeSupply →
        PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply) ∧
      (PowerTwoFlexibleActualTerminalCarryCorridorEscapeSupply →
        PowerTwoActualLcmOrbitNonintegralitySupply) := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.terminalDominance_orbit_nonintegral in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem terminalDominance_orbit_nonintegral {a q : ℕ} (ha : 8 ≤ a)
    (hshort : 2 * q + 1 + 1 + (a + 6) < 2 * 2 ^ a)
    (hfit : 2 * ((periodLcm (2 ^ a) + q + 2 : ℕ) : ℤ) ≤ (4 : ℤ) ^ q)
    (hdom : diagonalWindowIncrement (2 ^ a) (2 * q + 1 + 1) ≤
      2 * actualOddHalfCenteredLift a q) :
    totientTail (2 * periodLcm (2 ^ a)) - totientTail (periodLcm (2 ^ a))
      ∉ Set.range ((↑) : ℤ → ℝ) := by
  sorry
/-- States prop:te-chain from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.topEdgeResidueGap_or_of_paperAdjacentSuffixMidband in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem topEdgeResidueGap_or_of_paperAdjacentSuffixMidband
    {a m : ℕ}
    (hroom :
      ((2 * periodLcm (2 ^ a) + m + 3 : ℕ) : ℤ) < (2 : ℤ) ^ m)
    (hlo :
      ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ) ≤
        diagonalAdjacentSuffixResidue (2 ^ a) 0 m)
    (hhi :
      diagonalAdjacentSuffixResidue (2 ^ a) 0 m ≤
        (2 : ℤ) ^ m -
          ((2 * periodLcm (2 ^ a) + m + 2 : ℕ) : ℤ)) :
    ActualLcmTopEdgeResidueGap a 0 m m ∨
      ActualLcmTopEdgeResidueGap a 0 (m + 1) m := by
  sorry
/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientTail_enclosure in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientTail_enclosure (n : ℕ) (hn : 1 ≤ n) :
    0 ≤ totientTail n ∧ totientTail n ≤ (n : ℝ) + 1 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAX
