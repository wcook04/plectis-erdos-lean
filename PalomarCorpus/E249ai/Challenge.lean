/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #249, band i

Erdős problem #249 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E249` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Topology

namespace PalomarCorpus.E249.PaperStatementsAI
open Filter
open Topology
/-- States catalogue:cert:d1, prop:D1D2-inv from the long record for Erdős problem #249. Transported from Erdos249257.irrational_of_den_mul_abs_sub_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_den_mul_abs_sub_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in atTop, ((u k : ℝ)) ≠ x)
    (h0 : Tendsto (fun k => ((u k).den : ℝ) * |x - (u k : ℝ)|) atTop (nhds 0)) :
    Irrational x := by
  sorry
/-- States catalogue:cert:d2, prop:D1D2-inv from the long record for Erdős problem #249. Transported from Erdos249257.irrational_of_int_mul_near_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_int_mul_near_int {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  sorry
/-- States catalogue:cert:d2, prop:D1D2-inv from the long record for Erdős problem #249. Transported from Erdos249257.irrational_of_pow_mul_near_int in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_pow_mul_near_int (b : ℕ) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  sorry
/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from Erdos249257.one_div_den_mul_den_le_abs_sub in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_div_den_mul_den_le_abs_sub {q r : ℚ} (h : q ≠ r) :
    (1 : ℝ) / ((q.den : ℝ) * (r.den : ℝ)) ≤ |(q : ℝ) - (r : ℝ)| := by
  sorry
/-- States prop:gapwindow from the long record for Erdős problem #249. Transported from Erdos249257.totient_carry_residue_window_1_240_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_carry_residue_window_1_240_eq :
    (∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r)) % 2 ^ 240
      = 1299094806818720335611738031537456208600423915562142231419225521361164904 := by
  sorry
/-- States catalogue:mob:a1a from the long record for Erdős problem #249. Transported from Erdos249257.totient_series_eq_half_add_moebius_mersenne_square in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_series_eq_half_add_moebius_mersenne_square :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' d : ℕ+, ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  sorry
/-- States prop:coprime from the long record for Erdős problem #249. Transported from Erdos249257.totient_series_eq_half_add_visible_coprime_pairs in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_series_eq_half_add_visible_coprime_pairs :
    (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n)
      = 1 / 2 + ∑' p : ℕ × ℕ, (if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0) := by
  sorry
/-- States thm:denommobsq from the long record for Erdős problem #249. Transported from Erdos249257.tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_moebius_div_two_pow_sub_one_sq_ne_int_div_of_den_le_39819823323350687661677887437915526 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 39819823323350687661677887437915526 →
      (∑' k : ℕ+, ((ArithmeticFunction.moebius (k : ℕ) : ℤ) : ℝ)
          / ((2 : ℝ) ^ (k : ℕ) - 1) ^ 2)
        ≠ (a : ℝ) / (d : ℝ) := by
  sorry
/-- States thm:denom from the long record for Erdős problem #249. Transported from Erdos249257.tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_totient_div_pow_two_ne_ratCast_of_den_le_79639646646701375323355774875831053 :
    ∀ p : ℚ, p.den ≤ 79639646646701375323355774875831053 →
      (∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n) ≠ (p : ℝ) := by
  sorry
/-- States prop:coprime from the long record for Erdős problem #249. Transported from Erdos249257.tsum_visible_coprime_pairs_eq_totient_series in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_visible_coprime_pairs_eq_totient_series :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, ((Nat.totient n : ℝ)) / (2 : ℝ) ^ n := by
  sorry
/-- States thm:denomcoprime from the long record for Erdős problem #249. Transported from Erdos249257.tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526 in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_visible_coprime_pairs_ne_int_div_of_den_le_39819823323350687661677887437915526 :
    ∀ (a : ℤ) (d : ℕ), 0 < d → d ≤ 39819823323350687661677887437915526 →
      (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2
          then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
        ≠ (a : ℝ) / (d : ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAI
