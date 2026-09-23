/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #249, record section 6.4: further exact identities (part 3 of 3)

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #249, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #249 remains open, and no theorem in
this entry decides it.
-/

open Module
open Matrix
open Filter
open Topology
open Classical
open Finset

namespace PalomarCorpus.E249.PaperStatementsBB
open Module
open Matrix
/-- The canonical channels through level `e`: the two zero-residue base channels, followed by every odd residue at levels `1,...,e`. Local copy of Erdos249257.TotientCanonicalIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientCanonicalIndex (e : ℕ) :=
  Fin 2 ⊕ Σ j : Fin e, Fin (2 ^ j.val)
/-- Every dyadic totient channel at levels `0,...,e`, before removing the even-residue repetitions. Local copy of Erdos249257.TotientKernelThroughLevelIndex, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable abbrev TotientKernelThroughLevelIndex (e : ℕ) :=
  Σ j : Fin (e + 1), Fin (2 ^ j.val)
/-- The `(j,r)` dyadic-kernel channel of Euler's totient, viewed over `ℚ`. Local copy of Erdos249257.totientKernelSeq, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientKernelSeq (j r : ℕ) : ℕ → ℚ := fun n =>
  Nat.totient (2 ^ j * n + r)
/-- The canonical family indexed without duplicate even-residue channels. Local copy of Erdos249257.canonicalTotientKernelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def canonicalTotientKernelFamily (e : ℕ) :
    TotientCanonicalIndex e → ℕ → ℚ
  | Sum.inl i => totientKernelSeq i.val 0
  | Sum.inr ⟨j, r⟩ => totientKernelSeq (j.val + 1) (2 * r.val + 1)
/-- The complete finite dyadic kernel through level `e`. Local copy of Erdos249257.totientKernelThroughLevelFamily, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientKernelThroughLevelFamily (e : ℕ) :
    TotientKernelThroughLevelIndex e → ℕ → ℚ
  | ⟨j, r⟩ => totientKernelSeq j.val r.val
/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.canonical_family_basis_through_level in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_family_basis_through_level (e : ℕ) (he : 1 ≤ e) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) ∧
      Submodule.span ℚ (Set.range (canonicalTotientKernelFamily e)) =
        Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e)) ∧
      finrank ℚ
          (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily e))) =
        2 ^ e + 1 := by
  sorry
/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.canonical_level_zero_channels in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem canonical_level_zero_channels :
    canonicalTotientKernelFamily 0 (Sum.inl 0) =
        (fun n : ℕ => (Nat.totient n : ℚ)) ∧
      canonicalTotientKernelFamily 0 (Sum.inl 1) =
        (fun n : ℕ => (Nat.totient (2 * n) : ℚ)) ∧
      Fintype.card (TotientCanonicalIndex 0) = 2 := by
  sorry
/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.card_canonical_dyadic_index in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_canonical_dyadic_index (e : ℕ) :
    Fintype.card (TotientCanonicalIndex e) = 2 ^ e + 1 := by
  sorry
/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.finrank_throughLevel_zero_eq_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem finrank_throughLevel_zero_eq_one :
    finrank ℚ
      (Submodule.span ℚ (Set.range (totientKernelThroughLevelFamily 0))) = 1 := by
  sorry
/-- States prop:D4-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.linearIndependent_canonical_dyadic_family in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem linearIndependent_canonical_dyadic_family (e : ℕ) :
    LinearIndependent ℚ (canonicalTotientKernelFamily e) := by
  sorry
end PalomarCorpus.E249.PaperStatementsBB

namespace PalomarCorpus.E249.PaperStatementsAJ
/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.card_visible_antidiagonal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_visible_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2).card
      = Nat.totient n := by
  sorry
/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.den_lower_bound_of_positive_error in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem den_lower_bound_of_positive_error {S u : ℚ} (hlt : u < S) {ε : ℝ}
    (herr : (S : ℝ) - (u : ℝ) ≤ ε) :
    (1 : ℝ) / ((u.den : ℝ) * ε) ≤ (S.den : ℝ) := by
  sorry
/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.denominator_bound_tendsto_atTop_iff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem denominator_bound_tendsto_atTop_iff {f : ℕ → ℝ} (hpos : ∀ N, 0 < f N) :
    Filter.Tendsto (fun N => 1 / f N) Filter.atTop Filter.atTop ↔
      Filter.Tendsto f Filter.atTop (nhds 0) := by
  sorry
/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_denominator_bound_vacuous in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_prefix_denominator_bound_vacuous (N : ℕ) :
    (1 : ℝ) / ((2 : ℝ) ^ N * (((N : ℝ) + 2) / (2 : ℝ) ^ N)) = 1 / ((N : ℝ) + 2) ∧
      1 / ((N : ℝ) + 2) ≤ 1 := by
  sorry
/-- States prop:C2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_exact_range in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem farey_window_1_240_exact_range :
    (∀ q : ℕ, 1 ≤ q → q ≤ 79639646646701375323355774875831053 →
        (q * ((∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r))
              % 2 ^ 240)) % 2 ^ 240 + q * 243 < 2 ^ 240) ∧
      ¬ ((79639646646701375323355774875831054 *
              ((∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r))
                % 2 ^ 240)) % 2 ^ 240
            + 79639646646701375323355774875831054 * 243 < 2 ^ 240) := by
  sorry
/-- States prop:C2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_range_magnitude in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem farey_window_1_240_range_magnitude :
    (796 : ℕ) * 10 ^ 32 ≤ 79639646646701375323355774875831053 ∧
      (79639646646701375323355774875831053 : ℕ) < 797 * 10 ^ 32 := by
  sorry
/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_basePower_dilation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_basePower_dilation {x : ℝ} (b₀ : ℕ)
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ n : ℕ, ∃ z : ℤ,
      0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
        |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)) :
    Irrational x := by
  sorry
/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_product_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_den_mul_error_product_tendsto_zero
    {x : ℝ} {u : ℕ → ℚ} {ε : ℕ → ℝ}
    (hne : ∀ j, ((u j : ℚ) : ℝ) ≠ x)
    (herr : ∀ j, |x - ((u j : ℚ) : ℝ)| ≤ ε j)
    (h0 : Filter.Tendsto (fun j => ((u j).den : ℝ) * ε j) Filter.atTop (nhds 0)) :
    Irrational x := by
  sorry
/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_tendsto_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_den_mul_error_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in Filter.atTop, ((u k : ℚ) : ℝ) ≠ x)
    (h0 : Filter.Tendsto (fun k => ((u k).den : ℝ) * |x - ((u k : ℚ) : ℝ)|)
      Filter.atTop (nhds 0)) :
    Irrational x := by
  sorry
/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_dirichlet_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_dirichlet_gap {x : ℝ}
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ m z : ℤ,
      0 < |(m : ℝ) * x - (z : ℝ)| ∧ |(m : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)) :
    Irrational x := by
  sorry
/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_mul_den_le_abs_diff in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_div_den_mul_den_le_abs_diff {x u : ℚ} (hne : x ≠ u) :
    (1 : ℝ) / ((x.den : ℝ) * (u.den : ℝ)) ≤ |(x : ℝ) - (u : ℝ)| := by
  sorry
/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.positive_antidiagonal_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem positive_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2) = ∅ := by
  sorry
/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.rational_gap_lower_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_gap_lower_bound {lo hi : ℚ} (hlt : lo < hi) :
    (1 : ℝ) / ((hi.den : ℝ) * (lo.den : ℝ)) ≤ (hi : ℝ) - (lo : ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAJ

namespace PalomarCorpus.E249.PaperStatementsAK
/-- States prop:C3-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_int_div_of_small_denominator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_series_ne_int_div_of_small_denominator (a : ℤ) (q : ℕ)
    (hq : 0 < q) (hle : q ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ) := by
  sorry
/-- States prop:C3-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_series_ne_reduced_fraction_of_small_denominator in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_series_ne_reduced_fraction_of_small_denominator (p : ℚ)
    (hden : p.den ≤ 79639646646701375323355774875831053) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (p : ℝ) := by
  sorry
/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_zero_eq_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totient_zero_eq_zero : Nat.totient 0 = 0 := by
  sorry
/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_eq_series_sub_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_pos_coprime_pairs_eq_series_sub_half :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then 1 / (2 : ℝ) ^ (q.1 + q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := by
  sorry
/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_coprime_pairs_product_form in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_pos_coprime_pairs_product_form :
    (∑' q : ℕ × ℕ, if 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2
        then (1 / (2 : ℝ) ^ q.1) * (1 / (2 : ℝ) ^ q.2) else 0)
      = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 := by
  sorry
/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.visible_antidiagonal_one in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem visible_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2)
      = {((1 : ℕ), (0 : ℕ))} := by
  sorry
end PalomarCorpus.E249.PaperStatementsAK

namespace PalomarCorpus.E249.PaperStatementsAI
open Filter
open Topology
/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from Erdos249257.one_div_den_mul_den_le_abs_sub in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_div_den_mul_den_le_abs_sub {q r : ℚ} (h : q ≠ r) :
    (1 : ℝ) / ((q.den : ℝ) * (r.den : ℝ)) ≤ |(q : ℝ) - (r : ℝ)| := by
  sorry
end PalomarCorpus.E249.PaperStatementsAI

namespace PalomarCorpus.E249.PaperStatementsAL
open Classical
/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.SquareBlockBinary.basePower_dilation_not_universal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem basePower_dilation_not_universal :
    ∃ x : ℝ, Irrational x ∧ ∃ b₀ : ℕ, 2 ≤ b₀ ∧
      ¬ ∀ Q : ℤ, 1 ≤ Q → ∃ (n : ℕ) (z : ℤ),
          0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧
            |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ) := by
  sorry
end PalomarCorpus.E249.PaperStatementsAL

namespace PalomarCorpus.E249.PaperStatementsAT
open Finset
/-- The integer prefix `Φ_N = ∑_{n=0}^{N} φ(n)·2^{N-n}` of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientPrefix, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientPrefix (N : ℕ) : ℕ :=
  ∑ n ∈ Finset.range (N + 1), Nat.totient n * 2 ^ (N - n)
/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_den_dvd in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_prefix_den_dvd (N : ℕ) :
    (((totientPrefix N : ℤ) : ℚ) / (((2 : ℤ) ^ N : ℤ) : ℚ)).den ∣ 2 ^ N := by
  sorry
/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_tail_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadic_prefix_tail_le (N : ℕ) :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
        - (totientPrefix N : ℝ) / (2 : ℝ) ^ N
      ≤ ((N : ℝ) + 2) / (2 : ℝ) ^ N := by
  sorry
end PalomarCorpus.E249.PaperStatementsAT

namespace PalomarCorpus.E249.PaperStatementsAU
open Finset
/-- The local totient tail `R_N = ∑_{j≥0} φ(N+1+j)/2^{j+1} = ∑_{m≥1} φ(N+m)/2^m`: the fractional layer of `2^N · S`. Local copy of Erdos249257.TotientTailPeriodKiller.totientTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def totientTail (N : ℕ) : ℝ :=
  ∑' j : ℕ, (Nat.totient (N + 1 + j) : ℝ) / 2 ^ (j + 1)
/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientTail_le_add_two in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem totientTail_le_add_two (N : ℕ) :
    totientTail N ≤ (N : ℝ) + 2 := by
  sorry
end PalomarCorpus.E249.PaperStatementsAU
