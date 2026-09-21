/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.AdelicHeightObstruction`, `Erdos249257.BooleanMobiusCriticalCapacityCofinal`,
`Erdos249257.BooleanMobiusExactRowDichotomy`, `Erdos249257.HalfGreedyFatalGap`,
`Erdos249257.MaximalOmegaLayer`, `Erdos249257.RationalDenominatorSurvival`,
`ErdosProblems.Erdos257.PaperCompleteR20.QuotientRowIdentity`,
`ErdosProblems.Erdos257.PaperCompleteR21.CentredCompletionAndDecisionBoundary`,
`ErdosProblems.Erdos257.PaperCompleteR21.DenominatorBudget`,
`ErdosProblems.Erdos257.PaperCompleteR21.ExactRowDichotomyCountermodels`,
`ErdosProblems.Erdos257.PaperCompleteR21.LinearChannelAndMiddleCellExclusion`,
`ErdosProblems.Erdos257.PaperCompleteR21.PostTakeBandLocalisation`,
`ErdosProblems.Erdos257.PaperCompleteR21.ResetSqrtEscapeHalfMembership`,
`ErdosProblems.Erdos257.PaperCompleteR21.ScalarLocalisationHeightObstruction`,
`ErdosProblems.Erdos257.PaperCompleteR21.SeamRowGapAndCarry`,
`ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase`,
`ErdosProblems.Erdos257.PaperCompleteR21.SkipSafetyAndDivisorZeroRuns`,
`ErdosProblems.Erdos257.PaperCompleteR21.TruncatedRungWitnessHorizon`.
-/

namespace Erdos249257.ExternalVerification257PaperStatementsAA

noncomputable def mersenneTailLB3 (k : ℕ) : ℝ :=
  1 / 2 ^ k + 1 / (3 * (2 ^ k) ^ 2) + 1 / (7 * (2 ^ k) ^ 3)

noncomputable def primePowerLayer (p e : ℕ) (g : ℕ → ℤ) (n : ℕ) : ℤ :=
  g (p ^ e * n) - g (p ^ (e - 1) * n)

noncomputable def boundedDoubleOrRecycleModel (n : ℕ) : Prop := n = 6

noncomputable def Psi (L D x : ℕ) : ℚ :=
  ∑ d ∈ Finset.Icc 2 D, ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ x + i), (1 / 2 : ℚ) ^ i

noncomputable def Theta (L M : ℕ) : ℚ :=
  ∑ i ∈ Finset.Icc 1 L, (((M + i).divisors.card - 1 : ℕ) : ℚ) * (1 / 2 : ℚ) ^ i

noncomputable def iLeast (d M : ℕ) : ℕ := d - M % d

noncomputable def mCount (d M L : ℕ) : ℕ := ((Finset.Icc 1 L).filter (fun i => d ∣ M + i)).card

noncomputable def misalignMass (J M : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 2 J, (2 : ℝ) ^ (M % q) / (2 ^ q - 1)

noncomputable def resetCrossingBound (r : ℕ) : ℕ :=
  2 ^ ((r + 4) / 2) + 2 * r + 3

noncomputable def rowWeightSum (s : ℕ) (E : Finset ℕ) : ℤ :=
  ∑ e ∈ E, ⌊(4 : ℝ) ^ s / ((2 : ℝ) ^ e - 1)⌋

noncomputable def skipSum (S : Finset ℕ) : ℚ := ∑ d ∈ S, 1 / ((2 : ℚ) ^ d - 1)

noncomputable def truncLcm (J : ℕ) : ℕ := (Finset.Icc 2 J).lcm id

noncomputable def truncTail (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / (2 ^ (q * n) * (2 ^ q - 1))

noncomputable def truncWeight (J n : ℕ) : ℝ :=
  ∑ q ∈ Finset.Icc 1 J, (1 : ℝ) / 2 ^ (q * n)

/-- States lem:linear-channel-nogo from the long record for Erdős problem #257. Transported from
Erdos249257.AdelicHeightObstruction.linearDescender_eq_smul_eval in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem linearDescender_eq_smul_eval
    {V W : Type*} [AddCommGroup V] [Module ℚ V]
    [AddCommGroup W] [Module ℚ W]
    (ev : V →ₗ[ℚ] ℚ) (Λ : V →ₗ[ℚ] W)
    (hker : LinearMap.ker ev ≤ LinearMap.ker Λ)
    (he : ∃ e : V, ev e = 1) :
    ∃ w₀ : W, ∀ v : V, Λ v = ev v • w₀ := by
  sorry

/-- States lem:mixed-prime-power-layer, record:257rig-i5 from the long record for Erdős problem
#257. Transported from Erdos249257.MaximalOmegaLayer.primePowerLayer_comm in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem primePowerLayer_comm
    (p e q f : ℕ) (g : ℕ → ℤ) (n : ℕ) :
    primePowerLayer q f (primePowerLayer p e g) n =
      primePowerLayer p e (primePowerLayer q f g) n := by
  sorry

/-- States lem:denominator-survival from the long record for Erdős problem #257. Transported
from Erdos249257.RationalDenominatorSurvival.divisor_dvd_divInt_den in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem divisor_dvd_divInt_den
    {a : ℤ} {D m : ℕ} (hD : 0 < D) (hmD : m ∣ D)
    (hcop : Nat.Coprime m a.natAbs) :
    m ∣ (Rat.divInt a (D : ℤ)).den := by
  sorry

/-- States lem:denominator-survival from the long record for Erdős problem #257. Transported
from Erdos249257.RationalDenominatorSurvival.survivingDivisor_dvd_scaled_divInt_den in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem survivingDivisor_dvd_scaled_divInt_den
    {a : ℤ} {D C h : ℕ} (hD : 0 < D) (hCD : C ∣ D)
    (hcop : Nat.Coprime C a.natAbs) :
    C / Nat.gcd C h ∣
      (Rat.divInt ((h : ℤ) * a) (D : ℤ)).den := by
  sorry

/-- States record:257bm-c6b from the long record for Erdős problem #257. Transported from
Erdos249257.sub_two_le_two_pow_sub_four in the substantive development, whose statement was
refereed against the paper in the coverage ledger. -/
theorem sub_two_le_two_pow_sub_four
    {c : ℕ} (hc : 6 ≤ c) :
    c - 2 ≤ 2 ^ (c - 4) := by
  sorry

/-- States thm:master-identity from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR20.paper_master_identity_floors in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_master_identity_floors {n : ℕ} (hn : 6 ≤ n) (D : Finset ℕ)
    (hD : D ⊆ Finset.Ico 2 n) :
    ((2 : ℤ)^(2*n-1) - (2 : ℤ)^n -
      ∑ d ∈ D, ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋) - (2 : ℤ)^n =
    ((2 : ℤ)^(2*n-1) -
      ∑ d ∈ Finset.Ico 2 (2*n+1), ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋) +
      ∑ d ∈ (Finset.Ico 2 n) \ D, ⌊(4 : ℝ)^n / ((2 : ℝ)^d-1)⌋ := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.Psi_eq_of_residues_eq in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem Psi_eq_of_residues_eq (L D x y : ℕ) (h : ∀ d ∈ Finset.Icc 2 D, x % d = y % d) :
    Psi L D x = Psi L D y := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.card_divisors_sub_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem card_divisors_sub_one (n : ℕ) (hn : 1 ≤ n) :
    (n.divisors.card - 1 : ℕ) = (n.divisors.filter (fun d => 2 ≤ d)).card := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.dvd_add_iLeast in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem dvd_add_iLeast (d M : ℕ) (hd : 1 ≤ d) : d ∣ M + iLeast d M := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.geometric_term_eq_zero_of_lt_iLeast
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem geometric_term_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d)
    (h : L < iLeast d M) :
    (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
        / (1 - (1 / 2 : ℚ) ^ d) = 0 := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast_congr in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem iLeast_congr (d M M' : ℕ) (h : M % d = M' % d) : iLeast d M = iLeast d M' := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.iLeast_mem_Icc in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem iLeast_mem_Icc (d M : ℕ) (hd : 1 ≤ d) : 1 ≤ iLeast d M ∧ iLeast d M ≤ d := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.mCount_eq_zero_of_lt_iLeast
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem mCount_eq_zero_of_lt_iLeast (d M L : ℕ) (hd : 1 ≤ d) (h : L < iLeast d M) :
    mCount d M L = 0 := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.not_dvd_of_lt_iLeast in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem not_dvd_of_lt_iLeast (d M i : ℕ) (hd : 1 ≤ d) (hi : 1 ≤ i)
    (hlt : i < iLeast d M) : ¬ d ∣ M + i := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.residue_condition_iff in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem residue_condition_iff (d M i : ℕ) :
    ((i : ℤ) ≡ -(M : ℤ) [ZMOD (d : ℤ)]) ↔ d ∣ M + i := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.residue_cutoff_reading_fails
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem residue_cutoff_reading_fails :
    (∀ d ∈ Finset.Icc 2 (1 + 1), (1 : ℕ) % d = 3 % d) ∧ Theta 1 1 ≠ Theta 1 3 := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_Psi in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem theta_eq_Psi (M L D : ℕ) (hM : 1 ≤ M) (hD : M + L ≤ D) :
    Theta L M = Psi L D M := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_divisorResidueSum
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem theta_eq_divisorResidueSum (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => d ∣ M + i), (1 / 2 : ℚ) ^ i := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_geometricForm in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem theta_eq_geometricForm (M L D : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L)
    (hD : M + L ≤ D) :
    Theta L M
      = ∑ d ∈ Finset.Icc 2 D,
          (1 / 2 : ℚ) ^ (iLeast d M) * (1 - (1 / 2 : ℚ) ^ (d * mCount d M L))
            / (1 - (1 / 2 : ℚ) ^ d) := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_divisorResidue
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem theta_eq_tsum_divisorResidue (M L : ℕ) (hM : 1 ≤ M) (_hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          ∑ i ∈ (Finset.Icc 1 L).filter (fun i => (d + 2) ∣ M + i), (1 / 2 : ℚ) ^ i := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_eq_tsum_geometricForm
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem theta_eq_tsum_geometricForm (M L : ℕ) (hM : 1 ≤ M) (hL : 1 ≤ L) :
    Theta L M
      = ∑' d : ℕ,
          (1 / 2 : ℚ) ^ (iLeast (d + 2) M)
            * (1 - (1 / 2 : ℚ) ^ ((d + 2) * mCount (d + 2) M L))
            / (1 - (1 / 2 : ℚ) ^ (d + 2)) := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_one_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem theta_one_one : Theta 1 1 = 1 / 2 := by
  sorry

/-- States lem:odometer from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.ShortWindowDivisorPhase.theta_one_three in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem theta_one_three : Theta 1 3 = 1 := by
  sorry

/-- States lem:largest-false-rank-algebra from the long record for Erdős problem #257.
Transported from ErdosProblems.Erdos257.PaperCompleteR21.largest_false_rank_algebra in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem largest_false_rank_algebra {s d : ℕ} {u : Finset ℕ}
    (hd2 : 2 ≤ d) (hds : d < s) (hu : ∀ e ∈ u, 2 ≤ e ∧ e < d)
    (hlate : 2 * s < 3 * d) :
    3 * rowWeightSum s (u ∪ Finset.Ico (d + 1) s)
        + (3 * 2 ^ (s + 1) + 2 * 4 ^ (s - d) + 4)
      = 3 * rowWeightSum s (insert d u) := by
  sorry

/-- States record:257bm-k1 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_bounded_double_or_recycle_countermodel in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_bounded_double_or_recycle_countermodel :
    (∀ n : ℕ, boundedDoubleOrRecycleModel n ↔ n = 6) ∧
      boundedDoubleOrRecycleModel 6 ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        boundedDoubleOrRecycleModel (2 * n - 1) ∨
          ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ boundedDoubleOrRecycleModel (2 * c - 2)) ∧
      (∀ n : ℕ, 6 ≤ n → boundedDoubleOrRecycleModel n →
        4 ≤ 4 ∧ 4 ≤ n ∧ boundedDoubleOrRecycleModel (2 * 4 - 2)) ∧
      ¬ (∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ boundedDoubleOrRecycleModel n) := by
  sorry

/-- States prop:2adic-nogo from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_centred_completion_of_fixed_precision in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_centred_completion_of_fixed_precision
    (u : ℕ) (hu : 1 ≤ u) (m : ℕ) (v : ℕ → ℕ) (a : ℕ → ℤ)
    (hodd : ∀ i, i < m → Odd (a i)) (e₀ : ℤ) :
    ∃ e z : ℕ → ℤ, e 0 = e₀ ∧
      ∀ i, i < m →
        e (i + 1) = 2 * e i + 2 ^ (v i) * (a i + 2 ^ u * z i) ∧
          |e (i + 1)| ≤ 2 ^ (v i + u - 1) := by
  sorry

/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_dyadic_skip_test_iff in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_dyadic_skip_test_iff {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) :
    ((u : ℝ) / (2 * L) ≤ 1 / 2 ^ k) ↔ u ≤ a := by
  sorry

/-- States record:257bm-k1, record:257bm-k4 from the long record for Erdős problem #257.
Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_exists_seeded_bounded_double_or_recycle_model
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem paper_exists_seeded_bounded_double_or_recycle_model :
    ∃ P : ℕ → Prop,
      P 6 ∧
        (∀ n : ℕ, 6 ≤ n → P n →
          P (2 * n - 1) ∨ ∃ c : ℕ, 4 ≤ c ∧ c ≤ n ∧ P (2 * c - 2)) ∧
        ¬ ∀ N : ℕ, ∃ n : ℕ, N ≤ n ∧ P n := by
  sorry

/-- States cor:tr-half-lcm from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_half_lcm_horizon in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_half_lcm_horizon {J n : ℕ} (hJ : 2 ≤ J) (hn4 : 4 ≤ n)
    (hn : truncLcm J / 2 + 1 ≤ n) :
    ∃ M : ℕ, n ≤ M ∧ M + 2 ≤ 2 * n ∧ misalignMass J M < 11 / 15 := by
  sorry

/-- States cor:mersenne-height from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_mersenne_height in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_mersenne_height (x : ℚ) {r n : ℕ} (hx : 0 < x) (hn : 1 ≤ n)
    (hpow : 2 ^ r ∣ x.num.natAbs) (hlt : x < (2 : ℚ) / ((2 ^ n - 1 : ℕ) : ℚ)) :
    2 ^ r ≤ x.num.natAbs ∧
      x.num.natAbs * (2 ^ n - 1) < 2 * x.den ∧
      2 ^ r * (2 ^ n - 1) < 2 * x.den := by
  sorry

/-- States lem:tr-mod12 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_mod_twelve_filter in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_mod_twelve_filter {J M : ℕ} (hJ : 7 ≤ J)
    (hmu : misalignMass J M ≤ 11 / 15) : 12 ∣ M := by
  sorry

/-- States lem:tr-parity from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_parity_excludes_finite_support in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_parity_excludes_finite_support {J : ℕ} (hJ : 2 ≤ J)
    (A : Finset ℕ) (hA : ∀ n ∈ A, 2 ≤ n) :
    ∑ n ∈ A, truncWeight J n ≠ 1 / 2 := by
  sorry

/-- States record:257bm-k9 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_det_eq_zero in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_relationInvariant_channels_det_eq_zero
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    [Nontrivial ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    Matrix.det (fun i j : ι => channel j (row i)) = 0 := by
  sorry

/-- States record:257bm-k9 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_relationInvariant_channels_rank_le_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_relationInvariant_channels_rank_le_one
    {V ι : Type*} [AddCommGroup V] [Module ℚ V] [Fintype ι] [DecidableEq ι]
    (ev : V →ₗ[ℚ] ℚ) (channel : ι → V →ₗ[ℚ] ℚ)
    (hker : ∀ j : ι, LinearMap.ker ev ≤ LinearMap.ker (channel j))
    (row : ι → V) :
    ∃ u w : ι → ℚ, ∀ i j : ι, channel j (row i) = u i * w j := by
  sorry

/-- States lem:reverse-carry-word from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_reverse_carry_word in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_reverse_carry_word :
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ k L : ℕ, a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        u₁ (k + L + 1) - u₂ (k + L + 1) = 2 ^ L * (2 * (u₁ k - u₂ k) + 1) ∧
          Odd (2 * (u₁ k - u₂ k) + 1)) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B₁ B₂ : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B₁ →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B₂ →
        (2 : ℝ) ^ L ≤ B₁ + B₂) ∧
    (∀ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) →
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) →
      ∀ (k L : ℕ) (B : ℝ), a₁ k = a₂ k → b₁ k - b₂ k = 1 →
        (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) →
        (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) →
        |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B →
        (2 : ℝ) ^ L ≤ 2 * B) := by
  sorry

/-- States lem:scalar-localization from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_scalar_localization (x : ℚ) (c : ℤ) {H : ℕ}
    (hH : H ∣ x.den) (hscaled : ((c : ℚ) * x).den ∣ H) :
    0 < H ∧ x.den / H ∣ c.natAbs ∧ ((x.den / H : ℕ) : ℤ) ∣ c ∧
      (H : ℚ) * (c : ℚ) * x
        = ((c / ((x.den / H : ℕ) : ℤ) : ℤ) : ℚ) * (x.num : ℚ) := by
  sorry

/-- States lem:scalar-localization from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization_size_bound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_scalar_localization_size_bound (x : ℚ) {c : ℤ} {H : ℕ}
    (hH : H ∣ x.den) (hscaled : ((c : ℚ) * x).den ∣ H) (hc : c ≠ 0) :
    x.den / H ≤ c.natAbs := by
  sorry

/-- States lem:scalar-localization from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_scalar_localization_zero_degenerate in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_scalar_localization_zero_degenerate (x : ℚ) (H : ℕ) :
    (((0 : ℤ) : ℚ) * x).den = 1 ∧ x.den / H ∣ (0 : ℤ).natAbs ∧
      (0 : ℤ).natAbs = 0 := by
  sorry

/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_gives_three_over_three_t_sub_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_sharp_gives_three_over_three_t_sub_one {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u) (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) ≤ 3 / (3 * (2 : ℝ) ^ k - 1) := by
  sorry

/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_skip_safe_lb3 in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_skip_safe_lb3 {k u L a : ℕ}
    (hk : 1 ≤ k) (hu : 0 < u) (ha : 0 < a)
    (hdecomp : 2 ^ k * u + a = 2 * L + u)
    (hsharp : 2 * u ≤ 3 * a) :
    (u : ℝ) / (2 * L) < mersenneTailLB3 k := by
  sorry

/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_strictly_weaker_realizable in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_sharp_strictly_weaker_realizable :
    ∃ k u L a : ℕ, 1 ≤ k ∧ 0 < u ∧ 0 < a ∧
      2 ^ k * u + a = 2 * L + u ∧ 2 * u ≤ 3 * a ∧ ¬ u ≤ a := by
  sorry

/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_sharp_weaker_than_dyadic in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_sharp_weaker_than_dyadic {u a : ℕ} (h : u ≤ a) : 2 * u ≤ 3 * a := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #257.
Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_theoremA_crossing_bound_square_le in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_theoremA_crossing_bound_square_le (r : ℕ) (hr : 10 ≤ r) :
    resetCrossingBound r ^ 2 ≤ 2 ^ (r + 5) := by
  sorry

/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_three_channel_margin_identity in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_three_channel_margin_identity {t : ℝ} (ht : 2 ≤ t) :
    (1 / t + 1 / (3 * t ^ 2) + 1 / (7 * t ^ 3)) - 3 / (3 * t - 1) =
        (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1)) ∧
      0 < (2 * t - 3) / (21 * t ^ 3 * (3 * t - 1)) := by
  sorry

/-- States record:257hg-i4 from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_two_channels_insufficient in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_two_channels_insufficient :
    1 / (2 : ℝ) + 1 / (3 * (2 : ℝ) ^ 2) < 3 / (3 * (2 : ℝ) - 1) := by
  sorry

/-- States thm:two-thirds-band from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.paper_two_thirds_band in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_two_thirds_band :
    (∀ (R : ℚ) (k : ℕ), 0 < R → (1 / R ≤ 1 / 2 ^ k ↔ (2 : ℚ) ^ k ≤ R)) ∧
    (∀ R q : ℚ, 0 < R → R < q → 1 / (1 / R - 1 / q) = R * q / (q - R)) ∧
    (∀ R q m : ℚ, 0 < R → R < q → 1 ≤ m →
        ((m - 1 < R * q / (q - R) ∧ R * q / (q - R) < m) ↔
          (q * (m - 1) / (q + m - 1) < R ∧ R < q * m / (q + m)))) ∧
    (∀ q m : ℚ, 0 < q → 1 ≤ m →
        q * m / (q + m) - q * (m - 1) / (q + m - 1)
          = q ^ 2 / ((q + m) * (q + m - 1))) ∧
    (∀ b : ℕ, (2 : ℚ) ^ (b + 1) = 2 * ((2 : ℚ) ^ b - 1) + 2) ∧
    (∀ q : ℚ, 0 < q →
        2 * q * (q + 1) / (3 * q + 2) - q * (2 * q + 1) / (3 * q + 1)
            = q ^ 2 / ((3 * q + 1) * (3 * q + 2)) ∧
          q ^ 2 / ((3 * q + 1) * (3 * q + 2)) < 1 / 9) ∧
    (∀ R q : ℚ, 0 < q →
        (q * (2 * q + 1) / (3 * q + 1) < R ∧ R < 2 * q * (q + 1) / (3 * q + 2)) →
        2 * q < 3 * R ∧ 3 * R < 2 * q + 2 / 3) ∧
    (∀ (R q : ℚ) (mm n : ℤ), 0 < q → R = (mm : ℚ) → q = (n : ℚ) →
        ¬ (q * (2 * q + 1) / (3 * q + 1) < R ∧
          R < 2 * q * (q + 1) / (3 * q + 2))) ∧
    (∀ p D q : ℤ, 0 < p → 0 < D → 0 < q → Odd p → Odd D → Odd q →
        (q * (2 * q + 1) * p < 2 * D * (3 * q + 1) ∧
          2 * D * (3 * q + 2) < 2 * p * q * (q + 1)) →
        (4 : ℤ) ∣ (6 * D - 2 * p * q) ∧ 7 ≤ p) ∧
    (Odd (17 : ℤ) ∧ Odd (41 : ℤ) ∧ Odd (7 : ℤ) ∧ (∃ x y : ℤ, x * 17 + y * 41 = 1) ∧
      (2 : ℚ) ^ 3 - 1 = 7 ∧
      ((7 : ℚ) * (2 * 7 + 1) / (3 * 7 + 1) < (2 * 41 : ℚ) / 17 ∧
        (2 * 41 : ℚ) / 17 < 2 * 7 * (7 + 1) / (3 * 7 + 2))) := by
  sorry

/-- States thm:tr-witness-exclusion from the long record for Erdős problem #257. Transported
from ErdosProblems.Erdos257.PaperCompleteR21.paper_witness_exclusion in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_witness_exclusion {J n M : ℕ} (hJ : 3 ≤ J) (hn : 4 ≤ n)
    (hMlow : n ≤ M) (hMhigh : M + 2 ≤ 2 * n)
    (hmu : misalignMass J M ≤ 11 / 15)
    (D : Finset ℕ) (hD : ∀ d ∈ D, 2 ≤ d ∧ d + 1 ≤ n) :
    ¬ (truncTail J n < 1 / 2 - ∑ d ∈ D, truncWeight J d ∧
        1 / 2 - ∑ d ∈ D, truncWeight J d < truncWeight J n) := by
  sorry

/-- States lem:reverse-carry-word from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.reverse_carry_word_common_bound_sharp in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem reverse_carry_word_common_bound_sharp :
    ∃ (a₁ b₁ u₁ a₂ b₂ u₂ : ℕ → ℤ) (k L : ℕ) (B : ℝ),
      (∀ m : ℕ, b₁ m + 2 * u₁ m = a₁ m + u₁ (m + 1)) ∧
      (∀ m : ℕ, b₂ m + 2 * u₂ m = a₂ m + u₂ (m + 1)) ∧
      a₁ k = a₂ k ∧ b₁ k - b₂ k = 1 ∧
      (∀ j : ℕ, j < L → a₁ (k + 1 + j) = a₂ (k + 1 + j)) ∧
      (∀ j : ℕ, j < L → b₁ (k + 1 + j) = b₂ (k + 1 + j)) ∧
      |((u₁ (k + L + 1) : ℤ) : ℝ)| ≤ B ∧ |((u₂ (k + L + 1) : ℤ) : ℝ)| ≤ B ∧
      ¬ ((2 : ℝ) ^ L ≤ B) := by
  sorry

/-- States prop:exponent-gap from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.skipSum_den_dvd_prod in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem skipSum_den_dvd_prod (S : Finset ℕ) (hS : ∀ d ∈ S, 1 ≤ d) :
    ((skipSum S).den : ℤ) ∣ ∏ d ∈ S, ((2 : ℤ) ^ d - 1) := by
  sorry

/-- States prop:exponent-gap from the long record for Erdős problem #257. Transported from
ErdosProblems.Erdos257.PaperCompleteR21.weighted_denominator_budget in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
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

end Erdos249257.ExternalVerification257PaperStatementsAA
