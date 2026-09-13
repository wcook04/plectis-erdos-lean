/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.ZudilinHeightRegion
import Solutions.PalomarCorpus.E1049.Statement

namespace PalomarCorpus.E1049.PublishedHeightRegions

theorem threeHalves_zudilin_power_obstruction :
    3 ^ 81 < 2 ^ 200 :=
  ErdosProblems.Erdos1049.threeHalves_zudilin_power_obstruction

theorem eightyOneTwoHundredths_lt_threeHalves_log_ratio :
    (81 : ℝ) / 200 < Real.log 2 / Real.log 3 :=
  ErdosProblems.Erdos1049.eightyOneTwoHundredths_lt_threeHalves_log_ratio

theorem threeHalves_outside_zudilinHeightRegion :
    ¬ ZudilinHeightRegion 3 2 := by
  simpa [ZudilinHeightRegion, ErdosProblems.Erdos1049.ZudilinHeightRegion] using
    ErdosProblems.Erdos1049.threeHalves_outside_zudilinHeightRegion

theorem threeHalves_outside_bundschuhVaananenHeightRegion :
    ¬ BundschuhVaananenHeightRegion 3 2 := by
  simpa [BundschuhVaananenHeightRegion,
    ErdosProblems.Erdos1049.BundschuhVaananenHeightRegion] using
    ErdosProblems.Erdos1049.threeHalves_outside_bundschuhVaananenHeightRegion

end PalomarCorpus.E1049.PublishedHeightRegions
