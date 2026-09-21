/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperWeightedRefinementsR10
import Solutions.PalomarCorpus.E1041ab.Statement

open scoped BigOperators
open scoped ComplexConjugate
open Real
open Complex
open Polynomial
open Set

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsAB

theorem paper_weighted_free_point : WeightedFreePoint := @ErdosProblems.Erdos1041.paper_weighted_free_point

end PalomarCorpus.E1041.PaperStatementsAB
