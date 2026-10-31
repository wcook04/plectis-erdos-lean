/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.MersenneLambertLadder
import Solutions.PalomarCorpus.E257_18.Statement

open ArithmeticFunction

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E257.PaperStatementsAJ

theorem tsum_moebius_div_two_pow_sub_one_eq_half :
    ∑' d : ℕ+, ((moebius (d : ℕ) : ℤ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) = 1 / 2 := @MersenneLambertLadder.tsum_moebius_div_two_pow_sub_one_eq_half

end PalomarCorpus.E257.PaperStatementsAJ
