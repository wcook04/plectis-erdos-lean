/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #257, record sections 2.4 to 2.5: the size of the required error bounds; what finite certificates decide

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #257, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #257 remains open, and no theorem in
this entry decides it.
-/

open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory

namespace PalomarCorpus.E257_04.Shared
/-- The real Mersenne weight 1 divided by 2 to the power n minus 1; at n = 0 the value is 0 because division by zero is zero here. -/
noncomputable def mersenneWeight (n : ℕ) : ℝ :=
  1 / ((2 : ℝ) ^ n - 1)
/-- The Mersenne tail beyond rank n, namely the sum over k at least 0 of the Mersenne weight at n+k+1. -/
noncomputable def mersenneTail (n : ℕ) : ℝ :=
  ∑' k : ℕ, mersenneWeight (n + k + 1)
/-- The real number coded by a set A of exponents, namely the sum over a in A with a at least 1 of 1 divided by 2 to the power a minus 1; the indexing runs over k and evaluates the indicator at k+1, so only positive exponents contribute. -/
noncomputable def positiveMersenneSupportValue (A : Set ℕ) : ℝ :=
  ∑' k : ℕ, Set.indicator A mersenneWeight (k + 1)
end PalomarCorpus.E257_04.Shared

namespace PalomarCorpus.E257.PaperStatementsA
open Filter
open Set
/-- The exact binary affine orbit driven by the fresh coefficient word `a`. Local copy of Erdos249257.affineBinaryOrbit, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def affineBinaryOrbit (a : ℕ → ℤ) (u0 : ℤ) : ℕ → ℤ
  | 0 => u0
  | n + 1 => 2 * affineBinaryOrbit a u0 n - a (n + 1)
/-- States prop:local-void from the long record for Erdős problem #257. Transported from Erdos249257.affineBinaryOrbit_mod_twoPow_eq in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem affineBinaryOrbit_mod_twoPow_eq (a : ℕ → ℤ) (u0 v0 : ℤ) (L : ℕ) :
    affineBinaryOrbit a u0 L ≡ affineBinaryOrbit a v0 L [ZMOD (2 : ℤ) ^ L] := by
  sorry
end PalomarCorpus.E257.PaperStatementsA

namespace PalomarCorpus.E257.PaperStatementsAA
/-- The finite Mersenne sum associated with a skip set. Local copy of ErdosProblems.Erdos257.PaperCompleteR21.skipSum, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def skipSum (S : Finset ℕ) : ℚ := ∑ d ∈ S, 1 / ((2 : ℚ) ^ d - 1)
/-- States prop:2adic-nogo from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_centred_completion_of_fixed_precision in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_centred_completion_of_fixed_precision
    (u : ℕ) (hu : 1 ≤ u) (m : ℕ) (v : ℕ → ℕ) (a : ℕ → ℤ)
    (hodd : ∀ i, i < m → Odd (a i)) (e₀ : ℤ) :
    ∃ e z : ℕ → ℤ, e 0 = e₀ ∧
      ∀ i, i < m →
        e (i + 1) = 2 * e i + 2 ^ (v i) * (a i + 2 ^ u * z i) ∧
          |e (i + 1)| ≤ 2 ^ (v i + u - 1) := by
  sorry
/-- States prop:exponent-gap from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.skipSum_den_dvd_prod in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem skipSum_den_dvd_prod (S : Finset ℕ) (hS : ∀ d ∈ S, 1 ≤ d) :
    ((skipSum S).den : ℤ) ∣ ∏ d ∈ S, ((2 : ℤ) ^ d - 1) := by
  sorry
/-- States prop:exponent-gap from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.weighted_denominator_budget in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem weighted_denominator_budget (n : ℕ) (hn : 2 ≤ n) (S : Finset ℕ)
    (hS : S ⊆ Finset.Ico 2 n) :
    Real.logb 2 (((skipSum S).den : ℕ) : ℝ)
        ≤ ∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1) ∧
      (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) ≤ ∑ d ∈ S, (d : ℝ) ∧
      (∑ d ∈ S, (d : ℝ)) ≤ (n : ℝ) * ((n : ℝ) - 1) / 2 - 1 ∧
      (S.Nonempty →
        (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) < ∑ d ∈ S, (d : ℝ)) ∧
      (S = ∅ → (∑ d ∈ S, Real.logb 2 ((2 : ℝ) ^ d - 1)) = 0 ∧
        (∑ d ∈ S, (d : ℝ)) = 0) := by
  sorry
end PalomarCorpus.E257.PaperStatementsAA

namespace PalomarCorpus.E257.PaperStatementsAE
open Filter
open Set
/-- The radius of the balanced-pulse family at location `m`. Local copy of Erdos249257.balancedPulseRadius, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2
/-- A two-site pulse whose mass can be moved from position `m` to `m+1` without changing its binary-series value. Local copy of Erdos249257.balancedPulseCoeff, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0
/-- States prop:local-void from the long record for Erdős problem #257. Transported from Erdos249257.balancedPulse_endpoint_fanout in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_endpoint_fanout (m r : ℕ) :
    balancedPulseCoeff m r (m + 1) / 2 = r := by
  sorry
/-- States prop:local-void from the long record for Erdős problem #257. Transported from Erdos249257.balancedPulse_label_card_lower_bound in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_label_card_lower_bound
    {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ)
    (decode : Λ → ℕ) (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ := by
  sorry
/-- States prop:local-void from the long record for Erdős problem #257. Transported from Erdos249257.balancedPulse_no_autonomous_decoder in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r := by
  sorry
/-- States prop:finite-state-nogo, prop:local-void from the long record for Erdős problem #257. Transported from Erdos249257.balancedPulse_weighted_pair in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_weighted_pair
    {m r : ℕ} (hr : r ≤ balancedPulseRadius m) :
    2 * balancedPulseCoeff m r m + balancedPulseCoeff m r (m + 1) =
      2 * balancedPulseRadius m := by
  sorry
end PalomarCorpus.E257.PaperStatementsAE

namespace PalomarCorpus.E257.PaperStatementsAM
open Filter
open Set
open Topology
open scoped ENNReal
open MeasureTheory
export PalomarCorpus.E257_04.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- A finite half-gap witness in the cut-locator coordinates. Local copy of Erdos249257.ExistsFatalHalfGap, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def ExistsFatalHalfGap : Prop :=
  ∃ (u : Finset ℕ) (d : ℕ), (∀ n ∈ u, 0 < n ∧ n ≤ d) ∧
    positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail (d + 1)
      < 1 / 2 ∧
    (1 / 2 : ℝ) < positiveMersenneSupportValue (↑u : Set ℕ)
      + mersenneWeight (d + 1)
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
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_iff_exists_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem existsFatalHalfGap_iff_exists_certificate :
    ExistsFatalHalfGap ↔ ∃ p : List Bool × ℕ, FatalHalfGapCertificate p := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.existsFatalHalfGap_of_certificate in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem existsFatalHalfGap_of_certificate {L : List Bool} {N : ℕ}
    (h : FatalHalfGapCertificate (L, N)) : ExistsFatalHalfGap := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.mersenneTail_eq_sum_add in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem mersenneTail_eq_sum_add (m K : ℕ) :
    mersenneTail m
      = (∑ j ∈ Finset.range K, mersenneWeight (m + 1 + j)) + mersenneTail (m + K) := by
  sorry
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.scaledMersenneWeight_cast in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem scaledMersenneWeight_cast {N n : ℕ} (hn : 0 < n) (hnN : n ≤ N) :
    (scaledMersenneWeight N n : ℝ) = 2 * (mersenneDen N : ℝ) * mersenneWeight n := by
  sorry
end PalomarCorpus.E257.PaperStatementsAM

namespace PalomarCorpus.E257.PaperStructuresS
open scoped ENNReal
open Filter
open Set
open MeasureTheory
open Topology
export PalomarCorpus.E257_04.Shared (mersenneTail mersenneWeight positiveMersenneSupportValue)
/-- **Packet §4.** A finite support word certified to straddle the target at depth `d`: the coded value is at most `t` and the value plus the complete unresolved tail mass still reaches `t`. This is deliberately *weaker* than the `HalfPrefixForcingChain.interval_trapped` containment condition: overlap of the correction image with the cylinder, not containment inside it. Local copy of Erdos249257.IsStraddlePrefix, restated so the compared statements elaborate against Mathlib alone. -/
structure IsStraddlePrefix (t : ℝ) (u : Finset ℕ) (d : ℕ) : Prop where
  mem_bounds : ∀ n ∈ u, 0 < n ∧ n ≤ d
  value_le : positiveMersenneSupportValue (↑u : Set ℕ) ≤ t
  le_value_add_tail :
    t ≤ positiveMersenneSupportValue (↑u : Set ℕ) + mersenneTail d
/-- The Mersenne achievement set, with the analytically invisible zero bit normalized away. Local copy of Erdos249257.mersenneAchievementSet, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def mersenneAchievementSet : Set ℝ :=
  {x : ℝ | ∃ A : Set ℕ, 0 ∉ A ∧ x = positiveMersenneSupportValue A}
/-- States thm:one-sided from the long record for Erdős problem #257. Transported from ErdosProblems.Erdos257.PaperCompleteR21.paper_one_sidedness in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_one_sidedness :
    (∃ P : ℕ → Prop, ComputablePred P ∧
        ((1 / 2 : ℝ) ∉ mersenneAchievementSet ↔ ∃ n : ℕ, P n) ∧
        ((1 / 2 : ℝ) ∈ mersenneAchievementSet ↔ ∀ n : ℕ, ¬ P n)) ∧
      (∀ d : ℕ, ∃ x : ℝ, IsStraddlePrefix x ∅ d ∧ x ∉ mersenneAchievementSet) := by
  sorry
end PalomarCorpus.E257.PaperStructuresS
