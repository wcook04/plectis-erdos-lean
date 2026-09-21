/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band i

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
open Matrix
open Topology

namespace PalomarCorpus.E249.PaperStatementsBI
open Module
open Filter
open Set
open Matrix
open Topology
/-- The exact integer recurrence together with the subexponential boundary `u(N) = o(2^N)`, expressed as convergence of the quotient. Local copy of Erdos249257.IsTemperedBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)
/-- The full carry-section family through levels `1,...,e`. Local copy of Erdos249257.TotientCarryIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))
/-- Every dyadic totient channel at levels `0,...,e`, before removing the even-residue repetitions. Local copy of Erdos249257.TotientKernelThroughLevelIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)
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
/-- The `(j,r)` dyadic-kernel channel of Euler's totient, viewed over `ℚ`. Local copy of Erdos249257.totientKernelSeq, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)
/-- The complete finite dyadic kernel through level `e`. Local copy of Erdos249257.totientKernelThroughLevelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val
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
/-- States prop:D5cons from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.rank_floor_and_false_proposed_carryRank_ceiling in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rank_floor_and_false_proposed_carryRank_ceiling :
    (∀ e : ℕ, 1 ≤ e →
        finrank ℚ
            (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)))
          = 2 ^ e + 1)
      ∧ (¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) →
          ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
            IsTemperedBinaryOrbit Nat.totient v u
              ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                  finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e))))
      ∧ (∀ g : ℕ → ℕ,
          (∀ v : ℕ, ∀ u : ℕ → ℤ, 0 < v →
              IsTemperedBinaryOrbit Nat.totient v u →
              ∀ e : ℕ,
                finrank ℚ
                    (Submodule.span ℚ
                      (Set.range (canonicalCarryKernelFamily u e)))
                  ≤ g e) →
          (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1) →
          Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))
      ∧ ((∀ n : ℕ, control n ≤ n)
          ∧ binaryCoeffSeries control = 5 / 4
          ∧ ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
              IsTemperedBinaryOrbit control v u
                ∧ ∀ e : ℕ, 2 ^ e - 1 ≤
                    finrank ℚ
                      (Submodule.span ℚ
                        (Set.range (canonicalCarryKernelFamily u e))))
      ∧ ¬ ∃ g : ℕ → ℕ,
          (∃ e : ℕ, 1 ≤ e ∧ g e < 2 ^ e - 1)
            ∧ ∀ (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ),
                (∀ n : ℕ, c n ≤ n) →
                ¬ Irrational (binaryCoeffSeries c) →
                0 < v →
                IsTemperedBinaryOrbit c v u →
                ∀ e : ℕ,
                  finrank ℚ
                      (Submodule.span ℚ
                        (Set.range (canonicalCarryKernelFamily u e)))
                    ≤ g e := by
  sorry
end PalomarCorpus.E249.PaperStatementsBI
