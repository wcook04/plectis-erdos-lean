/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Erdos249257.GenericTailOrbitRigidity
import Erdos249257.TotientCarryKernelRigidity
import Erdos249257.TotientTailCarryPeriod
import ErdosProblems.Erdos249.PaperCompleteR21.DyadicSectionBasisAndRationalCarry
import ErdosProblems.Erdos249.PaperCompleteR21.GenericCarryRankCeilingCounterexample
import ErdosProblems.Erdos249.PaperCompleteR21.TailCarryPeriodAndRankFloor

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GenericTailOrbitRigidity`, `Erdos249257.TotientCarryKernelRigidity`,
`Erdos249257.TotientTailCarryPeriod`,
`ErdosProblems.Erdos249.PaperCompleteR21.DyadicSectionBasisAndRationalCarry`,
`ErdosProblems.Erdos249.PaperCompleteR21.GenericCarryRankCeilingCounterexample`,
`ErdosProblems.Erdos249.PaperCompleteR21.TailCarryPeriodAndRankFloor`.
-/

open Module
open Filter
open Set

namespace Erdos249257.ExternalVerification249PaperStatementsBH

noncomputable def CarrySectionsEventuallyPeriodicMod
    (v h N₀ : ℕ) (u : ℕ → ℤ) : Prop :=
  ∀ j r n : ℕ, N₀ ≤ n →
    u (2 ^ j * n + r) ≡ u (2 ^ j * (n + h) + r) [ZMOD (v : ℤ)]

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

theorem no_generic_rationality_carryRank_ceiling :
    ¬ ∃ g : ℕ → ℕ,
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
                  ≤ g e := @ErdosProblems.Erdos249.PaperCompleteR21.no_generic_rationality_carryRank_ceiling

theorem rationalControl_periodic_with_unbounded_carry_rank :
    ∃ c : ℕ → ℕ, (∀ n, c n ≤ n) ∧ binaryCoeffSeries c = 5 / 4 ∧
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
        IsTemperedBinaryOrbit c v u ∧
          CarrySectionsEventuallyPeriodicMod v 2 2 u ∧
          ∀ e : ℕ, 2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e))) := @ErdosProblems.Erdos249.PaperCompleteR21.rationalControl_periodic_with_unbounded_carry_rank

theorem rationality_forces_mod_period_and_unbounded_rank
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ, 2 ^ e - 1 ≤
            Module.finrank ℚ
              (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := @ErdosProblems.Erdos249.PaperCompleteR21.rationality_forces_mod_period_and_unbounded_rank hrat

theorem rationality_gives_mod_period_and_unbounded_rank
    (hrat : ¬ Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)) :
    ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ,
      IsTemperedBinaryOrbit Nat.totient v u ∧
        (∀ e : ℕ, 2 ^ e - 1 ≤
          Module.finrank ℚ
            (Submodule.span ℚ (Set.range (canonicalCarryKernelFamily u e)))) ∧
        ∃ h : ℕ, 0 < h ∧ ∃ N₀ : ℕ,
          CarrySectionsEventuallyPeriodicMod v h N₀ u := @ErdosProblems.Erdos249.PaperCompleteR21.rationality_gives_mod_period_and_unbounded_rank hrat

end Erdos249257.ExternalVerification249PaperStatementsBH
