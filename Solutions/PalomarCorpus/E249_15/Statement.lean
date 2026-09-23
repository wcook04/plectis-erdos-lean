/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_15

Every non-theorem declaration of `PalomarCorpus/E249_15/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Finset
open Filter
open Set
open Module
open scoped BigOperators
open ArithmeticFunction

namespace PalomarCorpus.E249_15.Shared
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The shifted totient difference `φ(n + h) - φ(n)`, taken in `ℤ` through the cast from `ℕ`. -/
noncomputable def deltaTotient (h n : ℕ) : ℤ := (Nat.totient (n + h) : ℤ) - (Nat.totient n : ℤ)
/-- The quotient of the first multiple of `d` strictly above `N`. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleQuotient, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleQuotient (N d : ℕ) : ℕ := N / d + 1
/-- The least strictly positive shift from `N` to a multiple of `d` when `d > 0`. At a divisor of `N` it is `d`, rather than zero. Local copy of Erdos249257.TotientShiftedMobiusPulse.forwardMultipleShift, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def forwardMultipleShift (N d : ℕ) : ℕ := d - N % d
/-- The universal period `lcm(1, 2, ..., t)`, given recursively by `periodLcm 0 = 1` and `periodLcm (t + 1) = lcm (periodLcm t) (t + 1)`. -/
noncomputable def periodLcm : ℕ → ℕ
  | 0 => 1
  | t + 1 => Nat.lcm (periodLcm t) (t + 1)
/-- The height `H_a = lcm(1, 2, ..., 2 ^ a)`, used as both the basepoint and the shift of the power-of-two LCM diagonal. -/
noncomputable def actualLcmHeight (a : ℕ) : ℕ :=
  periodLcm (2 ^ a)
/-- The binary totient tail `R_N = ∑_{j ≥ 1} φ(N + j) / 2 ^ j`, a real number satisfying `2 ^ N S = Φ_N + R_N`, where `S = ∑_{n ≥ 1} φ(n) / 2 ^ n` and `Φ_N = ∑_{n ≤ N} φ(n) 2 ^ (N - n)` is an integer. It obeys `0 < R_N ≤ N + 1` for `N ≥ 1`. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- The LCM diagonal orbit value `R_{2 H_a} - R_{H_a}`, the difference of the binary totient tails at the heights `2 H_a` and `H_a`. -/
noncomputable def actualLcmTailOrbit (a : ℕ) : ℝ :=
  totientTail (2 * actualLcmHeight a) - totientTail (actualLcmHeight a)
/-- The signed binary discrepancy `D_{h,N,L} = ∑_{j < L} (φ(N + h + 1 + j) - φ(N + 1 + j)) 2 ^ (L - 1 - j)` between two length-`L` totient windows separated by the shift `h`, an integer satisfying `|2 ^ L (R_{N + h} - R_N) - D_{h,N,L}| ≤ N + h + L + 2`. -/
noncomputable def windowDiscrepancy (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((Nat.totient (N + h + 1 + j) : ℤ) - (Nat.totient (N + 1 + j) : ℤ)) * 2 ^ (L - 1 - j)
/-- The decidable period-killer certificate: the residue of `A_{h,N,L}` modulo `2^L` avoids the radius-`(N+h+L+2)` neighbourhood of `0`. Local copy of Erdos249257.TotientTailPeriodKiller.certifiedKill, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedKill (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < windowDiscrepancy h N L % 2 ^ L ∧
    windowDiscrepancy h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)
end PalomarCorpus.E249_15.Shared

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
export PalomarCorpus.E249_15.Shared (actualLcmHeight actualLcmTailOrbit certifiedKill deltaTotient periodLcm totientTail windowDiscrepancy)
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
export PalomarCorpus.E249_15.Shared (actualLcmHeight actualLcmTailOrbit certifiedKill deltaTotient periodLcm totientTail windowDiscrepancy)
end PalomarCorpus.E249.PaperStatementsAU

namespace PalomarCorpus.E249.PaperStatementsBC
open Filter
open Set
open Finset
export PalomarCorpus.E249_15.Shared (IsTemperedBinaryOrbit totientTail)
end PalomarCorpus.E249.PaperStatementsBC

namespace PalomarCorpus.E249.PaperStatementsBH
open Module
open Filter
open Set
export PalomarCorpus.E249_15.Shared (IsTemperedBinaryOrbit)
/-- Uniform quotient-periodicity of all dyadic carry sections. The period is measured in the section variable; its ambient-index shift is `2^j h`. Local copy of Erdos249257.CarrySectionsEventuallyPeriodicMod, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CarrySectionsEventuallyPeriodicMod
    (v h N₀ : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j r n : ℕ, N₀ ≤ n →
    u (2 ^ j * n + r) ≡ u (2 ^ j * (n + h) + r) [ZMOD (v : ℤ)]
/-- The full carry-section family through levels `1,...,e`. Local copy of Erdos249257.TotientCarryIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))
/-- A dyadic section of an integer carry orbit, viewed over `ℚ`. Local copy of Erdos249257.carryKernelSeq, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)
/-- Every carry section through levels `1,...,e`, without quotienting or identifying residue channels. Local copy of Erdos249257.canonicalCarryKernelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val
end PalomarCorpus.E249.PaperStatementsBH

namespace PalomarCorpus.E249.PaperStatementsAJ
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsBA
open scoped BigOperators
open ArithmeticFunction
export PalomarCorpus.E249_15.Shared (forwardMultipleQuotient forwardMultipleShift)
end PalomarCorpus.E249.PaperStatementsBA

namespace PalomarCorpus.E249.PaperStatementsBM
open ArithmeticFunction
open scoped BigOperators
open Finset
export PalomarCorpus.E249_15.Shared (forwardMultipleQuotient forwardMultipleShift totientTail)
end PalomarCorpus.E249.PaperStatementsBM

namespace PalomarCorpus.E249.PaperStatementsAK
end PalomarCorpus.E249.PaperStatementsAK
