/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band b

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

namespace PalomarCorpus.E249.PaperStatementsB
/-- The closed-form cylinder mass at the coprime node `(a,b)`: `M(a,b) = 1/((2ᵃ-1)(2ᵇ-1)) = P(a ∣ X)·P(b ∣ Y)`. Local copy of GcdMomentCalculus.cylinderMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def cylinderMass (a b : ℕ+) : ℝ :=
  1 / (((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1))
/-- The depth-`d` finite unfolding of the mediant recursion: sum the stop mass `1/(2^{a+b}-1)` at every node of the first `d` generations of the subtree rooted at `(a,b)`, under the children `(a+b, b)` and `(a, a+b)`. Local copy of GcdMomentCalculus.sternBrocotDepthMass, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def sternBrocotDepthMass : ℕ → ℕ+ → ℕ+ → ℝ
  | 0, _, _ => 0
  | (dp + 1), a, b =>
      1 / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
        + sternBrocotDepthMass dp (a + b) b + sternBrocotDepthMass dp a (a + b)
/-- States catalogue:mob:a9b from the long record for Erdős problem #249. Transported from GcdMomentCalculus.sternBrocotDepthMass_error in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sternBrocotDepthMass_error (dp : ℕ) :
    ∀ a b : ℕ+,
      0 ≤ cylinderMass a b - sternBrocotDepthMass dp a b
        ∧ cylinderMass a b - sternBrocotDepthMass dp a b
            ≤ (2 / 3 : ℝ) ^ dp * cylinderMass a b := by
  sorry
/-- States catalogue:mob:a9b from the long record for Erdős problem #249. Transported from GcdMomentCalculus.tendsto_sternBrocotDepthMass in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tendsto_sternBrocotDepthMass (a b : ℕ+) :
    Filter.Tendsto (fun dp : ℕ => sternBrocotDepthMass dp a b)
      Filter.atTop (nhds (cylinderMass a b)) := by
  sorry
end PalomarCorpus.E249.PaperStatementsB
