/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Statement environment for Palomar entry E269e

Every non-theorem declaration of `PalomarCorpus/E269e/Challenge.lean`, verbatim and in
the same order, elaborated against Mathlib alone. The Solution modules import this file
instead of re-declaring or aliasing the definitions, so every constant that Comparator
walks from a compared theorem statement is byte-identical in the Challenge and Solution
environments. Generated from the Challenge; do not edit by hand.
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
end PalomarCorpus.E269.PaperStatementsE
