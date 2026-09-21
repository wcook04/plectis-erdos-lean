/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GenericTailOrbitRigidity`, `Erdos249257.TotientCarryKernelRigidity`,
`ErdosProblems.Erdos249.PaperCompleteR21.GenericCarryRankCeilingCounterexample`,
`ErdosProblems.Erdos249.ParityPerturbedRationalControl`.
-/

open Module
open Filter
open Set
open Topology

namespace Erdos249257.ExternalVerification249PaperStatementsBF

noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)

noncomputable abbrev TotientCarryIndex (e : ℕ) :=
  Σ j : Fin e, Fin (2 ^ (j.val + 1))

noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

noncomputable def carryKernelSeq (u : ℕ → ℤ) (j r : ℕ) : ℕ → ℚ := fun n =>
  u (2 ^ j * n + r)

noncomputable def canonicalCarryKernelFamily (u : ℕ → ℤ) (e : ℕ) :
    TotientCarryIndex e → ℕ → ℚ
  | ⟨j, r⟩ => carryKernelSeq u (j.val + 1) r.val

noncomputable abbrev S : ℝ := binaryCoeffSeries Nat.totient

noncomputable def xi : ℝ := 5 / 4 - S

noncomputable def digit (x : ℝ) : ℤ := ⌊4 * x + 2 / 3⌋

noncomputable def step (x : ℝ) : ℝ := 4 * x - (digit x : ℝ)

noncomputable def rem (x : ℝ) : ℕ → ℝ
  | 0 => x
  | m + 1 => step (rem x m)

noncomputable def dig (x : ℝ) (m : ℕ) : ℤ := digit (rem x m)

noncomputable def delta (n : ℕ) : ℤ :=
  if n % 2 = 0 ∧ 2 ≤ n then dig xi (n / 2 - 1) else 0

noncomputable def control (n : ℕ) : ℕ := ((Nat.totient n : ℤ) + delta n).toNat

/-- States prop:D5cons from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.fiveQuarter_comparison_rational_with_carryRank_floor
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem fiveQuarter_comparison_rational_with_carryRank_floor :
    (∀ n : ℕ, control n ≤ n)
      ∧ (∀ n : ℕ, n % 2 = 1 →
          control n = Nat.totient n)
      ∧ (∀ n : ℕ, := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsBF
