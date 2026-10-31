/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1041.PaperAnalyticTargets
import ErdosProblems.Erdos1041.PaperReflectedCompletion
import Solutions.PalomarCorpus.E1041_04.Statement

open Polynomial
open Set
open Filter
open Metric
open Bornology
open scoped BigOperators
open scoped ComplexConjugate
open scoped Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1041.PaperStatementsW
export PalomarCorpus.E1041_04.Shared (CriticalEnumeration RootsInClosedDisc)

theorem reflected_critical_value : ReflectedCriticalValue := @ErdosProblems.Erdos1041.PaperReflectedCompletion.reflected_critical_value

end PalomarCorpus.E1041.PaperStatementsW
