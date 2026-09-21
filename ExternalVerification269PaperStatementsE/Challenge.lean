/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #269

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos269.KernelCarryRank`,
`ErdosProblems.Erdos269.PaperR7AnalyticInterfaces`,
`ErdosProblems.Erdos269.PaperR8UniformRank`.
-/

open Set
open Metric
open scoped BigOperators
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ENNReal
open Polynomial

namespace Erdos249257.ExternalVerification269PaperStatementsE

noncomputable def logCarry (b x y : ℕ) : ℕ :=
  Nat.log b (x * y) - Nat.log b x - Nat.log b y

noncomputable def realCarryMatrix (p q r i j : ℕ) : ℝ :=
  ((r : ℝ)⁻¹) ^ logCarry r (p ^ i) (q ^ j)

noncomputable def FiniteSeparatedRank (A : ℕ → ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ f g : Fin d → ℕ → ℝ,
    ∀ i j, A i j = ∑ k : Fin d, f k i * g k j

noncomputable abbrev FiniteRankMatrix := {A : ℕ → ℕ → ℝ // FiniteSeparatedRank A}

noncomputable def uniformError (C A : ℕ → ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ i : ℕ, ⨆ j : ℕ, ENNReal.ofReal |C i j - A i j|

/-- States long269:res:uniform-rank from the long record for Erdős problem #269. Transported
from ErdosProblems.Erdos269.PaperR8.uniform_rank_complete in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem uniform_rank_complete {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpr : p ≠ r) (hqr : q ≠ r) :
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal ((1 - (r : ℝ)⁻¹) / 2) ∧
    (⨅ A : FiniteRankMatrix, uniformError (realCarryMatrix p q r) A.val) =
        ENNReal.ofReal (((r : ℝ) - 1) / (2 * (r : ℝ))) ∧
    ∃ A : FiniteRankMatrix,
      (∀ i j, A.val i j = (1 + (r : ℝ)⁻¹) / 2) ∧
      uniformError (realCarryMatrix p q r) A.val =
        (⨅ F : FiniteRankMatrix, uniformError (realCarryMatrix p q r) F.val) := by
  sorry

end Erdos249257.ExternalVerification269PaperStatementsE
