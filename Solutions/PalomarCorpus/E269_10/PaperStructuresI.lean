/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.DistinctHeightIrrationality
import Solutions.PalomarCorpus.E269_10.Statement

open Finset
open Filter
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E269.PaperStructuresI

theorem distinctHeightSum235_irrational : Irrational distinctHeightSum235 := by
  first
  | (exact @ErdosProblems.Erdos269.distinctHeightSum235_irrational; done)
  | (set_option smartUnfolding false in
      exact @ErdosProblems.Erdos269.distinctHeightSum235_irrational; done)
  | (apply ErdosProblems.Erdos269.distinctHeightSum235_irrational <;> assumption; done)
  | (simpa only [distinctHeightSum235, jumpPoints235, runningHeight235] using ErdosProblems.Erdos269.distinctHeightSum235_irrational; done)
  | (set_option smartUnfolding false in
      with_unfolding_all exact @ErdosProblems.Erdos269.distinctHeightSum235_irrational; done)
  | (with_unfolding_all exact @ErdosProblems.Erdos269.distinctHeightSum235_irrational; done)

end PalomarCorpus.E269.PaperStructuresI
