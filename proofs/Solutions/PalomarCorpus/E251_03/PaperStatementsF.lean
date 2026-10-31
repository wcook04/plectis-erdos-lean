/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos251.PaperFiniteCertificatesR7
import ErdosProblems.Erdos251.PaperNonconcentrationR7
import Solutions.PalomarCorpus.E251_03.Statement

open scoped BigOperators
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E251.PaperStatementsF
export PalomarCorpus.E251_03.Shared (FixedBlockNonconcentration ZeroDensity)

theorem denominator_floor_decimal : (10 ^ 177 : ℕ) < 2 ^ 589 := @ErdosProblems.Erdos251.PaperR7.denominator_floor_decimal

theorem finite_perturbation_stability
    (a b : ℕ → ℤ) (E : Finset ℤ)
    (ha : FixedBlockNonconcentration a)
    (hE : ∀ n, b n - a n ∈ E) :
    FixedBlockNonconcentration b := @ErdosProblems.Erdos251.PaperR7.finite_perturbation_stability a b E ha hE

end PalomarCorpus.E251.PaperStatementsF
