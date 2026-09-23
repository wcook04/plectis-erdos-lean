/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperCompleteR21.SimultaneousMahlerSystem
import Solutions.PalomarCorpus.E1049_05.Statement

open scoped LaurentSeries
open scoped PowerSeries
open scoped Polynomial
open scoped RatFunc
open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStatementsX
export PalomarCorpus.E1049_05.Shared (divisorLambert kpos kpos_pos subs)

theorem no_finite_simultaneous_two_three_system (hAB : AdamczewskiBell) :
    ¬ ∃ V : Submodule (RatFunc ℚ) ℚ⸨X⸩,
        Module.Finite (RatFunc ℚ) V ∧
        divisorLambert ∈ V ∧
        (∀ f ∈ V, subs 2 f ∈ V) ∧ (∀ f ∈ V, subs 3 f ∈ V) := @ErdosProblems.Erdos1049.PaperCompleteR21.no_finite_simultaneous_two_three_system hAB

end PalomarCorpus.E1049.PaperStatementsX
