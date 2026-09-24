/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_04

Every non-theorem declaration of `PalomarCorpus/E249_04/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open scoped BigOperators
open Matrix
open ArithmeticFunction
open Module
open Filter
open Topology

namespace PalomarCorpus.E249_04.Shared
/-- The atom of index `n` at rung `r` of the Möbius-Mersenne ladder, namely `μ(n + 1) / (2 ^ (n + 1) - 1) ^ r` with `μ` the Möbius function; the index is shifted so that `n = 0` carries the divisor `d = 1`. -/
noncomputable def mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The rung `Θ_r = ∑_{d ≥ 1} μ(d) / (2 ^ d - 1) ^ r` of the Möbius-Mersenne ladder, defined as the real sum of the atoms above. The divisor convolution `φ = μ * id` gives `Θ_2 = S - 1/2` for the binary totient series `S = ∑_{n ≥ 1} φ(n) / 2 ^ n`. At `r = 0` the family is not summable and the Lean sum takes its default value `0`; every compared theorem uses the ladder only at `r ≥ 1`. -/
noncomputable def mobiusMersenneTheta (r : ℕ) : ℝ :=
  ∑' n : ℕ, mobiusMersenneTerm r n
end PalomarCorpus.E249_04.Shared

namespace PalomarCorpus.E249.PaperStatementsI
open Finset
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

namespace PalomarCorpus.E249.PaperStatementsJ
open scoped BigOperators
open Matrix
open ArithmeticFunction
export PalomarCorpus.E249_04.Shared (mobiusMersenneTerm mobiusMersenneTheta)
end PalomarCorpus.E249.PaperStatementsJ

namespace PalomarCorpus.E249.PaperStatementsK
open ArithmeticFunction
/-- Coefficient of `q^n` in the Möbius companion `M_mu(q^r)`. Local copy of IncidenceQuotientHermitePade.mobiusCompanionCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusCompanionCoeff (r n : ℕ) : ℤ :=
  if r ∣ n then moebius (n / r) else 0
/-- The finite Möbius-incidence matrix on the positive jet coordinates `q, q^2, ..., q^N`. Columns are companion jets. Local copy of IncidenceQuotientHermitePade.incidenceMobiusMatrix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def incidenceMobiusMatrix (N : ℕ) : Matrix (Fin N) (Fin N) ℤ :=
  fun i j => mobiusCompanionCoeff (j.val + 1) (i.val + 1)
end PalomarCorpus.E249.PaperStatementsK

namespace PalomarCorpus.E249.PaperStatementsL
open Module
open Matrix
/-- The canonical channels through level `e`: the two zero-residue base channels, followed by every odd residue at levels `1,...,e`. Local copy of Erdos249257.TotientCanonicalIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)
/-- The `(j,r)` dyadic-kernel channel of Euler's totient, viewed over `ℚ`. Local copy of Erdos249257.totientKernelSeq, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)
/-- The canonical family indexed without duplicate even-residue channels. Local copy of Erdos249257.canonicalTotientKernelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)
end PalomarCorpus.E249.PaperStatementsL

namespace PalomarCorpus.E249.PaperStatementsO
open scoped BigOperators
open Matrix
open ArithmeticFunction
export PalomarCorpus.E249_04.Shared (mobiusMersenneTerm mobiusMersenneTheta)
/-- The `n`th atom of the Möbius--Mersenne power ladder, with the positive integer index shifted to `n + 1`. Local copy of Erdos257PeriodNoncollapse.SignedQMomentObstruction.mobiusMersenneTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SignedQMomentObstruction_mobiusMersenneTerm (r n : ℕ) : ℝ :=
  ((moebius (n + 1) : ℤ) : ℝ) /
    (((2 : ℝ) ^ (n + 1) - 1) ^ r)
/-- The first `Y` atoms of the Möbius--Mersenne rung `r`. Local copy of ErdosProblems.Erdos249.RankOneSubrankObstruction.mobiusMersennePrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mobiusMersennePrefix (Y r : ℕ) : ℝ :=
  ∑ n ∈ Finset.range Y, SignedQMomentObstruction_mobiusMersenneTerm r n
end PalomarCorpus.E249.PaperStatementsO

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- The four asserted coefficient properties of a sequence `c : ℕ → ℕ`: uniform boundedness, `c(n) ≤ n`, parity agreement with `φ` at every index, and the separated-carry form of aperiodicity together with genuine non-eventual-periodicity. Local copy of ErdosProblems.Erdos249.PaperCompleteR21.ParityComparisonProperties, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ParityComparisonProperties (c : ℕ → ℕ) : Prop :=
  (∀ n, c n ≤ 6) ∧ (∀ n, c n ≤ n) ∧ (∀ n, c n % 2 = Nat.totient n % 2) ∧
    (∀ N G K : ℕ, ∃ k : ℕ, N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        c (2 ^ (k + i + 3)) = 6 ∧ c (2 ^ (k + i + 3) + 1) = 0) ∧
    (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n)
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAD
open Finset
/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249.PaperStatementsAD

namespace PalomarCorpus.E249.PaperStatementsAK
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAI
open Filter
open Topology
end PalomarCorpus.E249.PaperStatementsAI
