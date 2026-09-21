/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Palomar challenge for Erdős problem #257, band m

Erdős problem #257 is open and nothing here decides it. Each theorem below
restates one refereed declaration of the paper-linked Lean development for this
problem, with the definitions its statement mentions copied in so the whole file
elaborates against Mathlib alone. The declaration documentation names the source
declaration each statement is transported from. This band is a packaging split of
`PalomarCorpus/E257` under the Challenge size ceiling; it does not replace it.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
/-- The real Mersenne weight `1 / (2^n - 1)`. Local copy of Erdos249257.mersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The value coded by a set of positive exponents. The sequence index is zero-based while the exponent supplied to the weight is `k+1`. Local copy of Erdos249257.positiveMersenneSupportValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
/-- The remaining mass after processing exponents `1, ..., n`. Local copy of Erdos249257.mersenneTail, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- A finite half-gap witness in the cut-locator coordinates. Local copy of Erdos249257.ExistsFatalHalfGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExistsFatalHalfGap : Prop :=
  ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
      < 1 / 2 ∧
    (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
      + mersenneWeight (d + 1)
/-- The Erdős–Borwein constant, expressed in the positive Mersenne-tail coordinate already used throughout this file. Local copy of Erdos249257.erdosBorweinMersenneConstant, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def erdosBorweinMersenneConstant : ℝ :=
  mersenneTail 0
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- One term of the binary coding of the achievement set. Local copy of Erdos249257.mersenneDigitTerm, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneDigitTerm (k : ℕ) (b : ℕ → Fin 2) : ℝ :=
  ((b k : ℕ) : ℝ) * mersenneWeight (k + 1)
/-- The positive gap between one Mersenne weight and the tail after it. Local copy of Erdos249257.mersenneGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneGap (n : ℕ) : ℝ :=
  mersenneWeight n - mersenneTail n
/-- The support value coded by a binary sequence. Local copy of Erdos249257.positiveMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def positiveMersenneDigitValue (b : ℕ → Fin 2) : ℝ :=
  ∑' k : ℕ, mersenneDigitTerm k b
/-- The common denominator `∏_{k=1}^{N} (2^k - 1)`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.mersenneDen, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneDen (N : ℕ) : ℕ := ∏ k ∈ Finset.range N, (2 ^ (k + 1) - 1)
/-- `2 * mersenneDen N * mersenneWeight n`, an exact natural number whenever `1 ≤ n ≤ N`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.scaledMersenneWeight, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def scaledMersenneWeight (N n : ℕ) : ℕ := (2 * mersenneDen N) / (2 ^ n - 1)
/-- The scaled rational upper bound for the tail `mersenneTail (d+1)`: the exact weights of ranks `d+2, …, N` plus the enclosure `mersenneTail N < mersenneWeight N`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.certifiedTailBound, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedTailBound (d N : ℕ) : ℕ :=
  (∑ j ∈ Finset.range (N - (d + 1)), scaledMersenneWeight N (d + 1 + 1 + j))
    + scaledMersenneWeight N N
/-- The scaled value of the finite word coded by a list of bits: bit `i` of the list selects the Mersenne exponent `i + 1`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.certifiedWordValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certifiedWordValue (L : List Bool) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range L.length,
    bif L.getD i false then scaledMersenneWeight N (i + 1) else 0
/-- The finite certificate: a bit word of length `d`, a cutoff `N ≥ d + 1`, and two exact natural-number inequalities saying that the coded word already overshoots `1/2` after the skip at rank `d + 1`. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.FatalHalfGapCertificate, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def FatalHalfGapCertificate (p : List Bool × ℕ) : Prop :=
  p.1.length + 1 ≤ p.2 ∧
    certifiedWordValue p.1 p.2 + certifiedTailBound p.1.length p.2 < mersenneDen p.2 ∧
      mersenneDen p.2 <
        certifiedWordValue p.1 p.2 + scaledMersenneWeight p.2 (p.1.length + 1)
/-- The finite Mersenne word coded by a list of bits. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.certWord, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def certWord (L : List Bool) : Finset ℕ :=
  ((Finset.range L.length).filter fun i => L.getD i false = true).image (· + 1)
/-- Binary digit strings supported on `J`. Local copy of ErdosProblems.Erdos257.SupportedMersenneDigits, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def SupportedMersenneDigits (J : Set ℕ) :=
  {b : ℕ → Fin 2 // ∀ k, k ∉ J → b k = 0}
/-- The ordinary Mersenne digit map restricted to a chosen support. Local copy of ErdosProblems.Erdos257.supportedMersenneDigitValue, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneDigitValue
    (J : Set ℕ) (b : SupportedMersenneDigits J) : ℝ :=
  positiveMersenneDigitValue b.1
/-- The achievement set obtained by allowing digits only on `J`. Local copy of ErdosProblems.Erdos257.supportedMersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def supportedMersenneAchievementSet (J : Set ℕ) : Set ℝ :=
  Set.range (supportedMersenneDigitValue J)
/-- States thm:master-dichotomy from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_iff_no_existsFatalHalfGap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ¬ ExistsFatalHalfGap := by
  sorry
/-- States thm:master-dichotomy from the long record for Erdős problem #257. Transported from Erdos249257.half_mem_mersenneAchievementSet_or_exists_fatal_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_mem_mersenneAchievementSet_or_exists_fatal_gap :
    (1 / 2 : ℝ) ∈ mersenneAchievementSet ∨
      ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
          < 1 / 2 ∧
        (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
          + mersenneWeight (d + 1) := by
  sorry
/-- States lem:half-endpoint-kills from the long record for Erdős problem #257. Transported from Erdos249257.half_ne_coe_finset_add_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem half_ne_coe_finset_add_mersenneTail
    (u : Finset ℕ) (d : ℕ) :
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
      ≠ (1 / 2 : ℝ) := by
  sorry
/-- States record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.mersenneGap_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneGap_le {n : ℕ} (hn : 0 < n) :
    mersenneGap n ≤ (2 / 3 : ℝ) * ((1 : ℝ) / 4) ^ n + 3 * ((1 : ℝ) / 8) ^ n := by
  sorry
/-- States lem:gap-mass-summability, record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.mersenneGap_tail_le in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneGap_tail_le (N : ℕ) :
    ∑' k : ℕ, mersenneGap (N + k + 1)
      ≤ (2 / 9 : ℝ) * ((1 : ℝ) / 4) ^ N + (3 / 7 : ℝ) * ((1 : ℝ) / 8) ^ N := by
  sorry
/-- States lem:half-endpoint-kills from the long record for Erdős problem #257. Transported from Erdos249257.positiveMersenneSupportValue_coe_finset_ne_half in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem positiveMersenneSupportValue_coe_finset_ne_half
    {u : Finset ℕ} (h0 : 0 ∉ u) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≠ (1 / 2 : ℝ) := by
  sorry
/-- States record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.summable_mersenneGap_shift in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem summable_mersenneGap_shift (N : ℕ) :
    Summable (fun k : ℕ => mersenneGap (N + k + 1)) := by
  sorry
/-- States lem:gap-mass-summability from the long record for Erdős problem #257. Transported from Erdos249257.summable_mersenneGap_succ in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem summable_mersenneGap_succ : Summable (fun k : ℕ => mersenneGap (k + 1)) := by
  sorry
/-- States lem:gap-mass-summability, record:257hg-i2 from the long record for Erdős problem #257. Transported from Erdos249257.tendsto_mersenneGap_tail_zero in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tendsto_mersenneGap_tail_zero :
    Tendsto (fun N : ℕ => ∑' k : ℕ, mersenneGap (N + k + 1)) atTop (nhds 0) := by
  sorry
/-- States thm:real-form from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.mersenne_constant_decimal in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenne_constant_decimal :
    (1066951524152917 : ℝ)/10^16 < erdosBorweinMersenneConstant-3/2 ∧
      erdosBorweinMersenneConstant-3/2 < (1066951524152918 : ℝ)/10^16 := by
  sorry
/-- States thm:topology from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.mersenne_topology_quantitative in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenne_topology_quantitative :
    |erdosBorweinMersenneConstant-(16067 : ℝ)/10000| < 1/20000 ∧
    1 < erdosBorweinMersenneConstant ∧
    Filter.Tendsto (fun n : ℕ ↦ (2 : ℝ)^n*mersenneTail n) Filter.atTop (nhds 1) := by
  sorry
/-- States thm:geometry, thm:topology from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.paper_achievement_geometry in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_achievement_geometry :
    IsCompact mersenneAchievementSet ∧ IsClosed mersenneAchievementSet ∧
    Perfect mersenneAchievementSet ∧ IsTotallyDisconnected mersenneAchievementSet ∧
    IsNowhereDense mersenneAchievementSet ∧ volume mersenneAchievementSet = 1 ∧
    convexHull ℝ mersenneAchievementSet = Icc 0 erdosBorweinMersenneConstant ∧
    Function.Injective positiveMersenneDigitValue ∧
    ∀ x ∈ mersenneAchievementSet, ∃! A : Set ℕ,
      0 ∉ A ∧ positiveMersenneSupportValue A = x := by
  sorry
/-- States thm:real-form from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR20.row_constant_eq_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem row_constant_eq_tail :
    erdosBorweinMersenneConstant-3/2 = mersenneTail 1-1/2 := by
  sorry
/-- States thm:seam-limit from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.abs_supportValue_sub_le_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem abs_supportValue_sub_le_mersenneTail {A B : Set ℕ} {K : ℕ}
    (h : ∀ d : ℕ, 1 ≤ d → d ≤ K → (d ∈ A ↔ d ∈ B)) :
    |positiveMersenneSupportValue A - positiveMersenneSupportValue B|
      ≤ mersenneTail K := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.certificate_of_existsFatalHalfGap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certificate_of_existsFatalHalfGap (h : ExistsFatalHalfGap) :
    ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.certifiedTailBound_cast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedTailBound_cast {d N : ℕ} (hdN : d + 1 ≤ N) :
    (certifiedTailBound d N : ℝ)
      = 2 * (mersenneDen N : ℝ) *
          ((∑ j ∈ Finset.range (N - (d + 1)), mersenneWeight (d + 1 + 1 + j))
            + mersenneWeight N) := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.certifiedWordValue_cast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem certifiedWordValue_cast {L : List Bool} {N : ℕ} (hLN : L.length ≤ N) :
    (certifiedWordValue L N : ℝ)
      = 2 * (mersenneDen N : ℝ) * ∑ n ∈ certWord L, mersenneWeight n := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.depth_prefix_interval_disjoint in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem depth_prefix_interval_disjoint {t : ℝ} {u v : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d) (hv : ∀ n ∈ v, 0 < n ∧ n ≤ d)
    (hut : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d)
    (hvt : positiveMersenneSupportValue (↑v : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑v : Set ℕ) + mersenneTail d) :
    u = v := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_iff_exists_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem existsFatalHalfGap_iff_exists_certificate :
    ExistsFatalHalfGap ↔ ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_of_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem existsFatalHalfGap_of_certificate {L : List Bool} {N : ℕ}
    (h : FatalHalfGapCertificate (L, N)) : ExistsFatalHalfGap := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_endpoint_bounds in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_gap_endpoint_bounds {A : Set ℕ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hagree : ∀ n : ℕ, 0 < n → n ≤ d → (n ∈ A ↔ n ∈ u)) :
    (d + 1 ∉ A →
        positiveMersenneSupportValue A
          ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)) ∧
      (d + 1 ∈ A →
        positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)
          ≤ positiveMersenneSupportValue A) := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_excludes_every_representation in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_gap_excludes_every_representation {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hu : ∀ n ∈ u, 0 < n ∧ n ≤ d)
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    ∀ A : Set ℕ, 0 ∉ A → positiveMersenneSupportValue A ≠ t := by
  sorry
/-- States lem:fatal-gap-exclusion from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.fatal_gap_within_prefix_interval in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem fatal_gap_within_prefix_interval {t : ℝ} {u : Finset ℕ} {d : ℕ}
    (hlo : positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1) < t)
    (hhi : t < positiveMersenneSupportValue (↑u : Set ℕ) + mersenneWeight (d + 1)) :
    positiveMersenneSupportValue (↑u : Set ℕ) ≤ t ∧
      t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d := by
  sorry
/-- States lem:no-ties from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.irrational_mersenneTail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_mersenneTail : ∀ n : ℕ, Irrational (mersenneTail n) := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.mersenneTail_eq_sum_add in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneTail_eq_sum_add (m K : ℕ) :
    mersenneTail m
      = (∑ j ∈ Finset.range K, mersenneWeight (m + 1 + j)) + mersenneTail (m + K) := by
  sorry
/-- States prop:achievement-set-topology from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_achievement_set_topology in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_achievement_set_topology :
    Continuous positiveMersenneDigitValue ∧
      Set.range positiveMersenneDigitValue = mersenneAchievementSet ∧
      IsCompact mersenneAchievementSet ∧
      IsClosed mersenneAchievementSet ∧
      Perfect mersenneAchievementSet ∧
      IsTotallyDisconnected mersenneAchievementSet ∧
      IsNowhereDense mersenneAchievementSet ∧
      volume mersenneAchievementSet = 1 := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_exact_mass_threshold in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_exact_mass_threshold {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ mersenneTail k ↔
        (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ≤ (a : ℝ) / u) ∧
      0 < (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) ∧
      (mersenneTail k)⁻¹ - ((2 : ℝ) ^ k - 1) < 2 / 3 := by
  sorry
/-- States thm:sharp-fatal-gap from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_fatal_gap in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_fatal_gap :
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ (u : ℝ) / (2 * L) < mersenneWeight k)) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        (0 < a ↔ ¬ (mersenneWeight k ≤ (u : ℝ) / (2 * L)))) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < L → 2 ^ k * u + a = 2 * L + u →
        ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k ↔ u ≤ a)) ∧
    (∀ k : ℕ, (1 : ℝ) / 2 ^ k + 1 / (3 * 4 ^ k) + 1 / (7 * 8 ^ k) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        2 * u ≤ 3 * a → (u : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ u a : ℕ, u ≤ a → 2 * u ≤ 3 * a) ∧
    ((2 : ℕ) ^ 2 * 7 + 5 = 2 * 13 + 7 ∧ 2 * 7 ≤ 3 * 5 ∧ ¬ (7 ≤ 5) ∧
      (1 : ℝ) / 2 ^ 2 < (7 : ℝ) / (2 * 13) ∧ (7 : ℝ) / (2 * 13) < mersenneTail 2) ∧
    (∀ k L : ℕ, 1 ≤ k → 2 ^ k * 3 + 2 ≠ 2 * L + 3) ∧
    (∀ k L a : ℕ, 1 ≤ k → 0 < a → 2 ^ k * 1 + a = 2 * L + 1 →
        (1 : ℝ) / (2 * L) < mersenneTail k) ∧
    (∀ k u L a : ℕ, 1 ≤ k → 0 < u → 0 < a → 2 ^ k * u + a = 2 * L + u →
        mersenneTail k < (u : ℝ) / (2 * L) →
        3 * a < 2 * u ∧ 2 ≤ u ∧ (Odd u → 3 ≤ u)) := by
  sorry
/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_actual_tail in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_skip_safe_actual_tail {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTail k := by
  sorry
/-- States the paper statement it is bound to from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_volume_supportedMersenneAchievementSet_dichotomy in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ENNReal) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧ volume (supportedMersenneAchievementSet J) = 0) := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.scaledMersenneWeight_cast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaledMersenneWeight_cast {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (scaledMersenneWeight N n : ℝ) = 2 * (mersenneDen N : ℝ) * mersenneWeight n := by
  sorry
/-- States thm:straddle-closed-set from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.straddle_all_depths_iff_mem in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem straddle_all_depths_iff_mem (t : ℝ) :
    (∀ d : ℕ, ∃ D : Finset ℕ, (∀ n ∈ D, 0 < n ∧ n ≤ d) ∧
        positiveMersenneSupportValue (↑D : Set ℕ) ≤ t ∧
        t ≤ positiveMersenneSupportValue (↑D : Set ℕ) + mersenneTail d) ↔
      t ∈ mersenneAchievementSet := by
  sorry
/-- States thm:straddle-closed-set from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.straddle_limiting_support_inputs in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem straddle_limiting_support_inputs :
    IsCompact mersenneAchievementSet ∧
      Filter.Tendsto mersenneTail Filter.atTop (nhds 0) := by
  sorry
/-- States thm:supported-dichotomy from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.perfect_supportedMersenneAchievementSet in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem perfect_supportedMersenneAchievementSet
    {J : Set ℕ} (hJ : J.Infinite) :
    Perfect (supportedMersenneAchievementSet J) := by
  sorry
/-- States thm:supported-dichotomy from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.supportedMersenneDigitValue_injective in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem supportedMersenneDigitValue_injective (J : Set ℕ) :
    Function.Injective (supportedMersenneDigitValue J) := by
  sorry
/-- States thm:supported-dichotomy from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_dichotomy in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem volume_supportedMersenneAchievementSet_dichotomy (J : Set ℕ) :
    (∃ F : Finset ℕ,
        J = (↑F : Set ℕ)ᶜ ∧
          volume (supportedMersenneAchievementSet J) =
            ((2 : ℝ≥0∞) ^ F.card)⁻¹) ∨
      (Jᶜ.Infinite ∧
        volume (supportedMersenneAchievementSet J) = 0) := by
  sorry
/-- States thm:supported-dichotomy from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem volume_supportedMersenneAchievementSet_eq_zero_of_compl_infinite
    {J : Set ℕ} (hJ : Jᶜ.Infinite) :
    volume (supportedMersenneAchievementSet J) = 0 := by
  sorry
end PalomarCorpus.E257.PaperStatementsAM
