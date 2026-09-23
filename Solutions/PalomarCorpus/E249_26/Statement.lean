/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_26

Every non-theorem declaration of `PalomarCorpus/E249_26/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Module
open Finset
open Filter
open Set
open scoped BigOperators
open Matrix

namespace PalomarCorpus.E249_26.Shared
/-- Index type for the carry sections through depth `e`: an entry `⟨j, r⟩` with `j < e` and `r < 2 ^ (j + 1)` names the section at level `j + 1` and residue `r`, so every residue is kept at each level. -/
noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))
/-- The dyadic section `n ↦ u (2 ^ j n + r)` of a carry sequence `u` at level `j` and residue `r`, with values in `ℚ` through the cast from `ℤ`. -/
noncomputable def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)
/-- The family of carry sections indexed by `TotientCarryIndex e`, sending `⟨j, r⟩` to `n ↦ u (2 ^ (j + 1) n + r)`. -/
noncomputable def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val
end PalomarCorpus.E249_26.Shared

namespace PalomarCorpus.E249.PaperStatementsBJ
open Module
open Finset
export PalomarCorpus.E249_26.Shared (TotientCarryIndex canonicalCarryKernelFamily carryKernelSeq)
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
end PalomarCorpus.E249.PaperStatementsBJ

namespace PalomarCorpus.E249.PaperStatementsBH
open Module
open Filter
open Set
export PalomarCorpus.E249_26.Shared (TotientCarryIndex canonicalCarryKernelFamily carryKernelSeq)
/-- Uniform quotient-periodicity of all dyadic carry sections. The period is measured in the section variable; its ambient-index shift is `2^j h`. Local copy of Erdos249257.CarrySectionsEventuallyPeriodicMod, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def CarrySectionsEventuallyPeriodicMod
    (v h N₀ : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j r n : ℕ, N₀ ≤ n →
    u (2 ^ j * n + r) ≡ u (2 ^ j * (n + h) + r) [ZMOD (v : ℤ)]
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
end PalomarCorpus.E249.PaperStatementsBH

namespace PalomarCorpus.E249.PaperStatementsAG
open Filter
/-- Lacunary spike ranks `2^(k+3)`, beginning at `8`. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.IsLargePowerTwo, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsLargePowerTwo (n : ℕ) : Prop :=
  ∃ k : ℕ, n = 2 ^ (k + 3)
/-- The zero-one indicator of the lacunary spike ranks. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.largePowerTwoBit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def largePowerTwoBit (n : ℕ) : ℕ := by
  classical
  exact if IsLargePowerTwo n then 1 else 0
/-- Rational base coefficients before adding zero-valued sparse carries. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.parityBaseWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def parityBaseWeight : ℕ → ℕ
  | 0 => 0
  | 1 => 1
  | 2 => 1
  | 3 => 2
  | _ => 4
/-- The parity countermodel. Natural subtraction is exact because every negative spike lands on a base coefficient `4`. Local copy of Erdos249257.TotientParityCoboundaryCountermodel.parityCoboundaryWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def parityCoboundaryWeight (n : ℕ) : ℕ :=
  parityBaseWeight n + 2 * largePowerTwoBit n -
    4 * largePowerTwoBit (n - 1)
end PalomarCorpus.E249.PaperStatementsAG

namespace PalomarCorpus.E249.PaperStatementsAJ
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAY
open scoped BigOperators
/-- The coefficient-side monomial matrix before residual column scaling. Local copy of Erdos249257.ResidualGaugeObstruction.phasePowerMatrix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def phasePowerMatrix
    {d : ℕ} (e : Fin d → ℕ) (z : Fin d → ℂ) :
    Matrix (Fin d) (Fin d) ℂ :=
  fun i j ↦ z j ^ e i
end PalomarCorpus.E249.PaperStatementsAY

namespace PalomarCorpus.E249.PaperStatementsBB
open Module
open Matrix
/-- The canonical channels through level `e`: the two zero-residue base channels, followed by every odd residue at levels `1,...,e`. Local copy of Erdos249257.TotientCanonicalIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)
/-- The full dyadic kernel index, with the canonical residue range `0 ≤ r < 2^j` at every level `j`. Local copy of Erdos249257.TotientDyadicKernelIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientDyadicKernelIndex := Σ j : ℕ, Fin (2 ^ j)
/-- Every dyadic totient channel at levels `0,...,e`, before removing the even-residue repetitions. Local copy of Erdos249257.TotientKernelThroughLevelIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)
/-- The `(j,r)` dyadic-kernel channel of Euler's totient, viewed over `ℚ`. Local copy of Erdos249257.totientKernelSeq, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)
/-- The canonical family indexed without duplicate even-residue channels. Local copy of Erdos249257.canonicalTotientKernelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)
/-- Every canonical dyadic section of Euler's totient. Local copy of Erdos249257.fullTotientKernelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def fullTotientKernelFamily : TotientDyadicKernelIndex → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j r.val
/-- The complete finite dyadic kernel through level `e`. Local copy of Erdos249257.totientKernelThroughLevelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val
end PalomarCorpus.E249.PaperStatementsBB
