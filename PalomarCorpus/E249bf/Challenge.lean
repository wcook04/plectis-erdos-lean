/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band f

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open Module
open Filter
open Set
open Topology

namespace PalomarCorpus.E249.PaperStatementsBF
open Module
open Filter
open Set
open Topology
/-- The binary coefficient series `X_c = ∑_{n≥1} c(n)/2^n`. Local copy of Erdos249257.binaryCoeffSeries, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)
/-- The binary totient series in the repository's coefficient-series coordinate: `∑' n, φ(n+1)/2^(n+1)`. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.S, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev S : ℝ := binaryCoeffSeries Nat.totient
/-- `ξ = 5/4 - S`, the quantity expanded in centred base four. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.xi, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def xi : ℝ := 5 / 4 - S
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
/-- The perturbation: the `m`-th centred digit at the even argument `2m`, zero at odd arguments and at `0`. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.delta, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def delta (n : ℕ) : ℤ :=
  if n % 2 = 0 ∧ 2 ≤ n then dig xi (n / 2 - 1) else 0
/-- The control coefficient sequence `c = φ + δ`. Local copy of ErdosProblems.Erdos249.ParityPerturbedRationalControl.control, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def control (n : ℕ) : ℕ := ((Nat.totient n : ℤ) + delta n).toNat
/-- States prop:D5cons from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.fiveQuarter_comparison_rational_with_carryRank_floor in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fiveQuarter_comparison_rational_with_carryRank_floor :
    (∀ n : ℕ, control n ≤ n)
      ∧ (∀ n : ℕ, n % 2 = 1 →
          control n = Nat.totient n)
      ∧ (∀ n : ℕ, := by
  sorry
end PalomarCorpus.E249.PaperStatementsBF
