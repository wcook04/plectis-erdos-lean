/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E249_13

Every non-theorem declaration of `PalomarCorpus/E249_13/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
-/

open Module
open Filter
open Set
open Topology
open Matrix

namespace PalomarCorpus.E249_13.Shared
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- Index type for the carry sections through depth `e`: an entry `⟨j, r⟩` with `j < e` and `r < 2 ^ (j + 1)` names the section at level `j + 1` and residue `r`, so every residue is kept at each level. -/
noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))
/-- The binary value `∑_{n ≥ 1} c(n) / 2 ^ n` of a natural-number coefficient sequence, written with the summation index shifted so that the term `n = 0` carries `c 1 / 2`. At `c = φ` it is the binary totient series `S`. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The binary totient series in the repository's coefficient-series coordinate: `∑' n, φ(n+1)/2^(n+1)`. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.S, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev S : ℝ := binaryCoeffSeries Nat.totient
/-- The dyadic section `n ↦ u (2 ^ j n + r)` of a carry sequence `u` at level `j` and residue `r`, with values in `ℚ` through the cast from `ℤ`. -/
noncomputable def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)
/-- The family of carry sections indexed by `TotientCarryIndex e`, sending `⟨j, r⟩` to `n ↦ u (2 ^ (j + 1) n + r)`. -/
noncomputable def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val
/-- The digit extracted from `x`: `⌊4x + 2/3⌋`. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.digit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def digit (x : ℝ) : ℤ := ⌊4 * x + 2 / 3⌋
/-- One centred base-four step: `x ↦ 4x - ⌊4x + 2/3⌋`. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.step, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def step (x : ℝ) : ℝ := 4 * x - (digit x : ℝ)
/-- Iterated remainders. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.rem, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def rem (x : ℝ) : ℕ → ℝ
  | 0 => x
  | m + 1 => step (rem x m)
/-- The `m`-th digit (`m ≥ 0`), carrying weight `4^{-(m+1)}`. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.dig, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def dig (x : ℝ) (m : ℕ) : ℤ := digit (rem x m)
/-- `ξ = 5/4 - S`, the quantity expanded in centred base four. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.xi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def xi : ℝ := 5 / 4 - S
/-- The perturbation: the `m`-th centred digit at the even argument `2m`, zero at odd arguments and at `0`. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.delta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def delta (n : ℕ) : ℤ :=
  if n % 2 = 0 ∧ 2 ≤ n then dig xi (n / 2 - 1) else 0
/-- The control coefficient sequence `c = φ + δ`. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.control, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def control (n : ℕ) : ℕ := ((Nat.totient n : ℤ) + delta n).toNat
end PalomarCorpus.E249_13.Shared

namespace PalomarCorpus.E249.PaperStatementsE
open Module
open Filter
open Set
open Topology
export PalomarCorpus.E249_13.Shared (IsTemperedBinaryOrbit S TotientCarryIndex binaryCoeffSeries canonicalCarryKernelFamily carryKernelSeq control delta dig digit rem step xi)
end PalomarCorpus.E249.PaperStatementsE

namespace PalomarCorpus.E249.PaperStatementsF
open Module
open Filter
open Set
open Matrix
open Topology
export PalomarCorpus.E249_13.Shared (IsTemperedBinaryOrbit S TotientCarryIndex binaryCoeffSeries canonicalCarryKernelFamily carryKernelSeq control delta dig digit rem step xi)
/-- Every dyadic totient channel at levels `0,...,e`, before removing the even-residue repetitions. Local copy of Erdos249257.TotientKernelThroughLevelIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)
/-- The `(j,r)` dyadic-kernel channel of Euler's totient, viewed over `ℚ`. Local copy of Erdos249257.totientKernelSeq, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)
/-- The complete finite dyadic kernel through level `e`. Local copy of Erdos249257.totientKernelThroughLevelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val
end PalomarCorpus.E249.PaperStatementsF
