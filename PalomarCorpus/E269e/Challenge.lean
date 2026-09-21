/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #269, band e

Erdős problem #269 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E269` under the Challenge size ceiling; it does not replace it.
-/

open Set
open Metric
open scoped BigOperators
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ENNReal
open Polynomial

namespace PalomarCorpus.E269.PaperStatementsE
open Set
open Metric
open scoped BigOperators
open scoped Topology
open scoped BoundedContinuousFunction
open scoped ENNReal
open Polynomial
/-- The binary carry of `Nat.log` across a product. Local copy of ErdosProblems.Erdos269.logCarry, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def logCarry (b x y : ℕ) : ℕ :=
  Nat.log b (x * y) - Nat.log b x - Nat.log b y
/-- The normalised real-valued carry matrix, using the actual integer-log carry. Local copy of ErdosProblems.Erdos269.PaperR7.realCarryMatrix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def realCarryMatrix (p q r i j : ℕ) : ℝ :=
  ((r : ℝ)⁻¹) ^ logCarry r (p ^ i) (q ^ j)
/-- Local copy of ErdosProblems.Erdos269.PaperR8.FiniteSeparatedRank, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FiniteSeparatedRank (A : ℕ → ℕ → ℝ) : Prop :=
  ∃ d : ℕ, ∃ f g : Fin d → ℕ → ℝ,
    ∀ i j, A i j = ∑ k : Fin d, f k i * g k j
/-- All finite-separated-rank matrices, with no bounded-factor restriction. Local copy of ErdosProblems.Erdos269.PaperR8.FiniteRankMatrix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev FiniteRankMatrix := {A : ℕ → ℕ → ℝ // FiniteSeparatedRank A}
/-- An extended supremum is essential: the real supremum convention at an unbounded set must not turn infinite error into zero. Local copy of ErdosProblems.Erdos269.PaperR8.uniformError, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def uniformError (C A : ℕ → ℕ → ℝ) : ℝ≥0∞ :=
  ⨆ i : ℕ, ⨆ j : ℕ, ENNReal.ofReal |C i j - A i j|
/-- States long269:res:uniform-rank from the long record for Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR8.uniform_rank_complete in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
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
end PalomarCorpus.E269.PaperStatementsE
