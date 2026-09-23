/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.GreedyAchievementSet
import Solutions.PalomarCorpus.E257_20.Statement

open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAH
export PalomarCorpus.E257_20.Shared (mersenneTail mersenneWeight)

noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0

noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n

theorem halfTwoChannelCap_lt_mersenneTail (n : ℕ) :
    halfTwoChannelCap n < mersenneTail n := @Erdos249257.halfTwoChannelCap_lt_mersenneTail n

theorem irrational_erdosBorweinMersenneConstant :
    Irrational erdosBorweinMersenneConstant := @Erdos249257.irrational_erdosBorweinMersenneConstant

theorem mersenneGap_pos {n : ℕ} (hn : 0 < n) :
    0 < mersenneGap n := @Erdos249257.mersenneGap_pos n hn

theorem mersenneTail_eq_weight_add (n : ℕ) :
    mersenneTail n = mersenneWeight (n + 1) + mersenneTail (n + 1) := @Erdos249257.mersenneTail_eq_weight_add n

theorem mersenneTail_le_two_mul_weight (n : ℕ) :
    mersenneTail n ≤ 2 * mersenneWeight (n + 1) := @Erdos249257.mersenneTail_le_two_mul_weight n

theorem mersenneTail_lt_weight {n : ℕ} (hn : 0 < n) :
    mersenneTail n < mersenneWeight n := @Erdos249257.mersenneTail_lt_weight n hn

theorem two_mul_mersenneWeight_succ_lt {n : ℕ} (hn : 0 < n) :
    2 * mersenneWeight (n + 1) < mersenneWeight n := @Erdos249257.two_mul_mersenneWeight_succ_lt n hn

end PalomarCorpus.E257.PaperStatementsAH
