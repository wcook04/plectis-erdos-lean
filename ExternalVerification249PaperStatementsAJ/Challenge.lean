/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #249

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.CompositeDilationDefect`, `Erdos249257.GapFareyBound`,
`Erdos249257.PrimeJumpWindow`, `Erdos249257.PrimitiveRationalGapSupply`,
`Erdos249257.TotientActualLcmTopEdgeStaircase`, `Erdos249257.TotientFixedRankLcmAsymptotic`,
`ErdosProblems.Erdos249.CyclotomicAnchoredKill`,
`ErdosProblems.Erdos249.PaperCompleteR20.FiniteCarryCorrespondence`,
`ErdosProblems.Erdos249.PaperCompleteR20.MobiusSquareReduction`,
`ErdosProblems.Erdos249.PaperCompleteR20.RationalSpacingCorrespondence`,
`ErdosProblems.Erdos249.PaperCompleteR21.ActualLcmShortWindowArithmetic`,
`ErdosProblems.Erdos249.PaperCompleteR21.CompositeDilationIdentity`,
`ErdosProblems.Erdos249.PaperCompleteR21.CoprimeLatticeSumsAndLambert`,
`ErdosProblems.Erdos249.PaperCompleteR21.DoublingOrbitTransferAndFullDepthPhase`,
`ErdosProblems.Erdos249.PaperCompleteR21.ExtremalOrderDirectedAndPulse`,
`ErdosProblems.Erdos249.PaperCompleteR21.FareyDenominatorFloorExtension`,
`ErdosProblems.Erdos249.PaperCompleteR21.FareyExactRangeAndDenominatorExclusion`,
`ErdosProblems.Erdos249.PaperCompleteR21.FareyGapDenominatorExclusion`,
`ErdosProblems.Erdos249.PaperCompleteR21.GeneralIrrationalityCriteriaAndGapBounds`,
`ErdosProblems.Erdos249.PaperCompleteR21.HarmonicGapAndFourTail`,
`ErdosProblems.Erdos249.PaperCompleteR21.MersennePrimeSupportAnchors`,
`ErdosProblems.Erdos249.PaperCompleteR21.NearIntegerIrrationalityCriterion`,
`ErdosProblems.Erdos249.PaperCompleteR21.PenultimateStaircaseAndRankCurvature`,
`ErdosProblems.Erdos249.PaperCompleteR21.PrimeJumpWitnessAndMersenneChannels`,
`ErdosProblems.Erdos249.PaperCompleteR21.RationalParityCountermodelProperties`,
`ErdosProblems.Erdos249.PaperCompleteR21.RationalTailPeriodWitnesses`,
`ErdosProblems.Erdos249.PaperCompleteR21.ScalarLocalisationAndInversePhaseGauge`,
`ErdosProblems.Erdos249.PaperCompleteR21.TotientBlockConcatenation`,
`ErdosProblems.Erdos249.PaperCompleteR21.TwoAdicPulseBlockAndMobiusInversion`,
`ErdosProblems.Erdos249.PrimeRayCyclotomicCurvature`.
-/

namespace Erdos249257.ExternalVerification249PaperStatementsAJ

noncomputable def compositeDilationDefect (A : Set ℕ) (a x : ℕ) : ℕ :=
  by
    classical
    exact ((a * x).divisors.filter fun d =>
      d ∈ A ∧ ¬ d ∣ x ∧ d ≠ a).card

noncomputable def primeJumpSharpRadius (H p L : ℕ) : ℤ :=
  3 * p * H + (p + 1) * (L + 2)

noncomputable def MiddleRankTotientExtremal (H j : ℕ) : Prop :=
  (Nat.totient (2 * H + j) < Nat.totient (H + j) ∧
      Nat.totient (2 * H + j) < Nat.totient (3 * H + j)) ∨
    (Nat.totient (H + j) < Nat.totient (2 * H + j) ∧
      Nat.totient (3 * H + j) < Nat.totient (2 * H + j))

noncomputable def DyadicMixedGuard (A : ℤ) (b : ℕ) : Prop :=
  let P : ℤ := (2 : ℤ) ^ b
  let r : ℤ := A % (2 : ℤ) ^ (b + 2)
  (P ≤ r ∧ r < 2 * P) ∨ (2 * P ≤ r ∧ r < 3 * P)

noncomputable def binaryCyclotomicLayer (n : ℕ) : ℕ :=
  ((Polynomial.cyclotomic n ℤ).eval (2 : ℤ)).natAbs

noncomputable def totientBlock (H N : ℕ) : ℤ :=
  ∑ j ∈ Finset.range H,
    (Nat.totient (N + 1 + j) : ℤ) * 2 ^ (H - 1 - j)

noncomputable def GapCertificate (N K q : ℕ) : Prop :=
  (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (N + r) * 2 ^ (K - r)) % 2 ^ K))
      % 2 ^ K + q * (N + K + 2) < 2 ^ K

noncomputable def FareyGapExclusionUnbounded : Prop :=
  ∀ Q : ℕ, ∃ K : ℕ, ∀ q : ℕ, 0 < q → q ≤ Q → GapCertificate 1 K q

noncomputable def ParityComparisonProperties (c : ℕ → ℕ) : Prop :=
  (∀ n, c n ≤ 6) ∧ (∀ n, c n ≤ n) ∧ (∀ n, c n % 2 = Nat.totient n % 2) ∧
    (∀ N G K : ℕ, ∃ k : ℕ, N < 2 ^ (k + 3) ∧
      ∀ i : ℕ, i < K →
        2 ^ (k + i + 3) + G < 2 ^ (k + i + 4) ∧
        c (2 ^ (k + i + 3)) = 6 ∧ c (2 ^ (k + i + 3) + 1) = 0) ∧
    (¬ ∃ p N : ℕ, 0 < p ∧ ∀ n : ℕ, N ≤ n → c (n + p) = c n)

noncomputable def BoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∀ q p : ℕ,
    q.Prime → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1

noncomputable def EventualBoundedDegreeOrderConsumer
    (C : ℕ → ℕ) (m d : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q p : ℕ,
    q.Prime → Q₀ ≤ q → p.Prime → p ∣ C (m * q) →
      ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1

noncomputable def FinitePrimeSupportEscape (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q)

noncomputable def PrimeRayLayerSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∃ Q₀ : ℕ, ∀ q : ℕ,
    q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q)

noncomputable def UnboundedPrimeDivisorSupply (C : ℕ → ℕ) (m : ℕ) : Prop :=
  ∀ B N₀ : ℕ, ∃ q p : ℕ,
    q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p

noncomputable def IsFirstGapFailure (V K H qstar : ℕ) : Prop :=
  (∀ q : ℕ, 0 < q → q < qstar → (q * V) % 2 ^ K + q * H < 2 ^ K) ∧
    ¬ ((qstar * V) % 2 ^ K + qstar * H < 2 ^ K)

/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from
Erdos249257.positive_rational_difference_lower_bound in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem positive_rational_difference_lower_bound
    {whole pfx : ℚ} (hpositive : pfx < whole) :
    (1 : ℝ) /
        (((whole.den * pfx.den : ℕ) : ℝ)) ≤
      (whole : ℝ) - (pfx : ℝ) := by
  sorry

/-- States catalogue:cert:b12, prop:B12cons from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR20.finite_carry_candidate_count in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem finite_carry_candidate_count (h N : ℕ) :
    (Finset.Icc (-(N + h + 1 : ℤ)) (N + h + 1)).card = 2 * (N + h + 1) + 1 := by
  sorry

/-- States prop:mobsq from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.moebius_three_values in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem moebius_three_values (d : ℕ) :
    ArithmeticFunction.moebius d = -1 ∨ ArithmeticFunction.moebius d = 0 ∨
      ArithmeticFunction.moebius d = 1 := by
  sorry

/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.rational_cross_numerator_positive in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_cross_numerator_positive {u v : ℚ} (h : u < v) :
    1 ≤ v.num * (u.den : ℤ) - u.num * (v.den : ℤ) := by
  sorry

/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.rational_difference_exact in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_difference_exact (u v : ℚ) :
    (v : ℝ) - u =
      ((v.num * (u.den : ℤ) - u.num * (v.den : ℤ) : ℤ) : ℝ) /
        ((v.den : ℝ) * u.den) := by
  sorry

/-- States catalogue:cert:d9 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.rational_error_denominator_bound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_error_denominator_bound {u v : ℚ} {ε : ℝ}
    (h : u < v) (he : (v : ℝ) - u ≤ ε) :
    1 / ((u.den : ℝ) * ε) ≤ v.den := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomicLayer_eventual_instance in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem binaryCyclotomicLayer_eventual_instance (m : ℕ) (hm : 0 < m) :
    EventualBoundedDegreeOrderConsumer binaryCyclotomicLayer m 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.binaryCyclotomic_allPrime_form_fails in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem binaryCyclotomic_allPrime_form_fails :
    ((Polynomial.cyclotomic 6 ℤ).eval 2).natAbs = 3 ∧ ¬ (6 ∣ 3 - 1) ∧
      ¬ BoundedDegreeOrderConsumer binaryCyclotomicLayer 2 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.boundedDegreeOrderConsumer_unfolded
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem boundedDegreeOrderConsumer_unfolded (C : ℕ → ℕ) (m d : ℕ) :
    BoundedDegreeOrderConsumer C m d ↔
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ C (m * q) →
        ∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ m * q ∣ p ^ k - 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.boundedOrder_witness_iff_orderOf_le
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem boundedOrder_witness_iff_orderOf_le {n p d : ℕ} (hn : 0 < n) (hp : 0 < p)
    (hcop : Nat.Coprime p n) :
    (∃ k : ℕ, 1 ≤ k ∧ k ≤ d ∧ n ∣ p ^ k - 1) ↔ orderOf ((p : ℕ) : ZMod n) ≤ d := by
  sorry

/-- States prop:route4 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.bracket_of_two_sided_separation in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bracket_of_two_sided_separation
    {c P m δ : ℝ} (_hc : 0 < c) (_hm0 : 0 ≤ m) (_hmP : m < P)
    (hδ : |δ| < c) (h1 : 2 * c < |m + δ|) (h2 : 2 * c < |m + δ - P|) :
    c < m ∧ m < P - c := by
  sorry

/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.card_visible_antidiagonal in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem card_visible_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ Nat.Coprime q.1 q.2).card
      = Nat.totient n := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.complementDenominator_dvd_scalar in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem complementDenominator_dvd_scalar
    (x : ℚ) (c : ℤ) {H : ℕ} (_hHpos : 0 < H) (hH : H ∣ x.den)
    (hscaled : ((c : ℚ) * x).den ∣ H) :
    ((x.den / H : ℕ) : ℤ) ∣ c := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_eq_zero_of_prime_support
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem composite_dilation_defect_eq_zero_of_prime_support (A : Set ℕ) {a x : ℕ}
    (ha : a ∈ A) (hAprime : ∀ d ∈ A, d.Prime) :
    compositeDilationDefect A a x = 0 := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem composite_dilation_defect_univ_six_one :
    ((6 * 1 : ℕ).divisors.filter
        fun d => (d ∈ (Set.univ : Set ℕ) ∧ ¬ d ∣ 1 ∧ d ≠ 6)) = ({2, 3} : Finset ℕ) := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.composite_dilation_defect_univ_six_one_card in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem composite_dilation_defect_univ_six_one_card :
    compositeDilationDefect (Set.univ : Set ℕ) 6 1 = 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeLattice_gcd_layer_total {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    ∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0)
      = (r / (1 - r)) ^ 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_gcd_layer_total_eq_one_iff in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeLattice_gcd_layer_total_eq_one_iff {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' g : ℕ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (r ^ (g + 1)) ^ (p.1 + p.2) else 0))
        = 1 ↔ r = 1 / 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_half_eq_series in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeLattice_halfOpen_half_eq_series :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then (1 / 2 : ℝ) ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_halfOpen_sum in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeLattice_halfOpen_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = ∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_half_eq_one
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem coprimeLattice_lambert_half_eq_one :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (1 / 2 : ℝ) ^ (p.1 + p.2) / (1 - (1 / 2 : ℝ) ^ (p.1 + p.2)) else 0) = 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_identity in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeLattice_lambert_identity {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          r ^ (p.1 + p.2) / (1 - r ^ (p.1 + p.2)) else 0)
      = (r / (1 - r)) ^ 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_lambert_rational in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeLattice_lambert_rational (s : ℚ) (hs0 : 0 ≤ s) (hs1 : s < 1) :
    ∃ v : ℚ, (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then
          (s : ℝ) ^ (p.1 + p.2) / (1 - (s : ℝ) ^ (p.1 + p.2)) else 0)
      = (v : ℝ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_plain_half_eq_series_sub_half in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeLattice_plain_half_eq_series_sub_half :
    (∑' p : ℕ × ℕ,
        if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then (1 / 2 : ℝ) ^ (p.1 + p.2) else 0)
        = (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2 ∧
      (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) - 1 / 2
        ≠ ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_positive_sum in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeLattice_positive_sum {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ Nat.Coprime p.1 p.2 then r ^ (p.1 + p.2) else 0)
      = (∑' n : ℕ, (Nat.totient (n + 1) : ℝ) * r ^ (n + 1)) - r := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprimeLattice_removed_pair in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprimeLattice_removed_pair (a b : ℕ) :
    ((0 < a ∧ Nat.Coprime a b) ∧ ¬ (0 < a ∧ 0 < b ∧ Nat.Coprime a b))
      ↔ (a = 1 ∧ b = 0) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.coprime_of_dvd_pow_sub_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem coprime_of_dvd_pow_sub_one {n p k : ℕ} (hp : 0 < p) (hk : 1 ≤ k)
    (hdvd : n ∣ p ^ k - 1) : Nat.Coprime p n := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_eval in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem cyclotomic_four_eval (x : ℤ) :
    (Polynomial.cyclotomic 4 ℤ).eval x = x ^ 2 + 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_four_two_pow_eq_cyclotomic_two in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem cyclotomic_four_two_pow_eq_cyclotomic_two (h : ℕ) :
    (Polynomial.cyclotomic 4 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 1 ∧
      (Polynomial.cyclotomic 2 ℤ).eval ((2 : ℤ) ^ (2 * h)) = 2 ^ (2 * h) + 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_layer_prime_order_decomposition_paper in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem cyclotomic_layer_prime_order_decomposition_paper {n p : ℕ}
    (hn : 0 < n) (hp : p.Prime)
    (hpdvd : p ∣ ((Polynomial.cyclotomic n ℤ).eval 2).natAbs) :
    ∃ a : ℕ, n = p ^ a * orderOf ((2 : ℕ) : ZMod p) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_eval_two_not_dvd_doubling_chain in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem cyclotomic_three_eval_two_not_dvd_doubling_chain :
    (Polynomial.cyclotomic 3 ℤ).eval 2 = 7 ∧
      orderOf ((2 : ℕ) : ZMod 7) = 3 ∧
      (∀ j : ℕ, ¬ (3 ∣ 2 ^ j)) ∧
      (∀ j : ℕ, ¬ (7 ∣ 2 ^ 2 ^ j - 1)) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.cyclotomic_three_two_pow in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem cyclotomic_three_two_pow (h : ℕ) :
    (Polynomial.cyclotomic 3 ℤ).eval ((2 : ℤ) ^ h) = 2 ^ (2 * h) + 2 ^ h + 1 := by
  sorry

/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.den_lower_bound_of_positive_error in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem den_lower_bound_of_positive_error {S u : ℚ} (hlt : u < S) {ε : ℝ}
    (herr : (S : ℝ) - (u : ℝ) ≤ ε) :
    (1 : ℝ) / ((u.den : ℝ) * ε) ≤ (S.den : ℝ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.den_mul_abs_sub_ge_one_div_den in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem den_mul_abs_sub_ge_one_div_den {q u : ℚ} (hqu : q ≠ u) :
    (1 : ℝ) / (q.den : ℝ) ≤ (u.den : ℝ) * |(q : ℝ) - (u : ℝ)| := by
  sorry

/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.denominator_bound_tendsto_atTop_iff in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem denominator_bound_tendsto_atTop_iff {f : ℕ → ℝ} (hpos : ∀ N, 0 < f N) :
    Filter.Tendsto (fun N => 1 / f N) Filter.atTop Filter.atTop ↔
      Filter.Tendsto f Filter.atTop (nhds 0) := by
  sorry

/-- States lem:orbit from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.doublingMap_iterate_apply in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem doublingMap_iterate_apply (α : ℝ) (N : ℕ) :
    (fun x : ℝ => 2 * x)^[N] α = 2 ^ N * α := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.dvd_pow_sub_one_iff_orderOf_dvd in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem dvd_pow_sub_one_iff_orderOf_dvd {n p k : ℕ} (hn : 0 < n) (hp : 0 < p) :
    n ∣ p ^ k - 1 ↔ orderOf ((p : ℕ) : ZMod n) ∣ k := by
  sorry

/-- States prop:TE-03-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.dyadicMixedGuard_iff_twoBitBand in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicMixedGuard_iff_twoBitBand (A : ℤ) (b : ℕ) :
    DyadicMixedGuard A b ↔
      ((2 : ℤ) ^ b ≤ A % (2 : ℤ) ^ (b + 2)
        ∧ A % (2 : ℤ) ^ (b + 2) < 3 * (2 : ℤ) ^ b) := by
  sorry

/-- States prop:TE-02-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.dyadicScale_unique_in_open_interval in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem dyadicScale_unique_in_open_interval {B : ℤ} {m₁ m₂ : ℕ}
    (h₁ : B < (2 : ℤ) ^ m₁) (h₁' : (2 : ℤ) ^ m₁ < 2 * B)
    (h₂ : B < (2 : ℤ) ^ m₂) (h₂' : (2 : ℤ) ^ m₂ < 2 * B) :
    m₁ = m₂ := by
  sorry

/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.dyadic_prefix_denominator_bound_vacuous in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem dyadic_prefix_denominator_bound_vacuous (N : ℕ) :
    (1 : ℝ) / ((2 : ℝ) ^ N * (((N : ℝ) + 2) / (2 : ℝ) ^ N)) = 1 / ((N : ℝ) + 2) ∧
      1 / ((N : ℝ) + 2) ≤ 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.eventual_orderConsumer_conclusions
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem eventual_orderConsumer_conclusions {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : EventualBoundedDegreeOrderConsumer C m d) :
    FinitePrimeSupportEscape C m ∧
      (∀ hsupply : PrimeRayLayerSupply C m, UnboundedPrimeDivisorSupply C m) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_clean_cyclotomic_anchor_paper in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exists_clean_cyclotomic_anchor_paper (h N₀ : ℕ) (hh : 0 < h) :
    ∃ q p : ℕ, q.Prime ∧ p.Prime ∧
      p ∣ ((Polynomial.cyclotomic (h * q) ℤ).eval 2).natAbs ∧
      Nat.Coprime p (h * q) ∧ h * q ∣ p - 1 ∧ N₀ ≤ p - 1 := by
  sorry

/-- States prop:CP-05-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_prime_totient_shift_four_mul_congr_two_mod_four
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem exists_prime_totient_shift_four_mul_congr_two_mod_four
    (h B : ℕ) (hh : 0 < h) :
    ∃ p : ℕ, B < p ∧ p.Prime ∧
      ((Nat.totient (p + 4 * h) : ℤ) - (Nat.totient p : ℤ)) ≡ (2 : ℤ) [ZMOD 4] := by
  sorry

/-- States prop:b7 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.exists_rational_parityComparison in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_rational_parityComparison :
    ∃ c : ℕ → ℕ, ParityComparisonProperties c ∧
      ¬ Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  sorry

/-- States prop:FR-01 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_ne_zero in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem extremal_order_curvature_ne_zero {H j : ℕ} (hH : 1 ≤ H)
    (hextremal : MiddleRankTotientExtremal H j) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) ≠ 0 := by
  sorry

/-- States prop:FR-01 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_neg in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem extremal_order_curvature_neg {H j : ℕ} (hH : 1 ≤ H)
    (hleft : Nat.totient (H + j) < Nat.totient (2 * H + j))
    (hright : Nat.totient (3 * H + j) < Nat.totient (2 * H + j)) :
    (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) < 0 := by
  sorry

/-- States prop:FR-01 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.extremal_order_curvature_pos in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem extremal_order_curvature_pos {H j : ℕ} (hH : 1 ≤ H)
    (hmin : Nat.totient (2 * H + j) < min (Nat.totient (H + j)) (Nat.totient (3 * H + j))) :
    0 < (Nat.totient (3 * H + j) : ℤ) - 2 * Nat.totient (2 * H + j) + Nat.totient (H + j) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.farey_gap_paper in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem farey_gap_paper {a b c d r s : ℤ} (hb : 0 < b) (hd : 0 < d)
    (hdet : b * c - a * d = 1) (hleft : a * s < r * b) (hright : r * d < c * s) :
    b + d ≤ s := by
  sorry

/-- States prop:C2-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_exact_range in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem farey_window_1_240_exact_range :
    (∀ q : ℕ, 1 ≤ q → q ≤ 79639646646701375323355774875831053 →
        (q * ((∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r))
              % 2 ^ 240)) % 2 ^ 240 + q * 243 < 2 ^ 240) ∧
      ¬ ((79639646646701375323355774875831054 *
              ((∑ r ∈ Finset.Icc 1 240, Nat.totient (1 + r) * 2 ^ (240 - r))
                % 2 ^ 240)) % 2 ^ 240
            + 79639646646701375323355774875831054 * 243 < 2 ^ 240) := by
  sorry

/-- States prop:C2-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.farey_window_1_240_range_magnitude in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem farey_window_1_240_range_magnitude :
    (796 : ℕ) * 10 ^ 32 ≤ 79639646646701375323355774875831053 ∧
      (79639646646701375323355774875831053 : ℕ) < 797 * 10 ^ 32 := by
  sorry

/-- States prop:C2sup from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.gapCertificate_window_1_240 in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gapCertificate_window_1_240 (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    GapCertificate 1 240 q := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_1_240_first_failure_paper in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem gapCheck_window_1_240_first_failure_paper :
    IsFirstGapFailure
      1299094806818720335611738031537456208600423915562142231419225521361164904
      240 243 79639646646701375323355774875831054 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_1_240_paper in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem gapCheck_window_1_240_paper (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904)
        % 2 ^ 240 + q * 243 < 2 ^ 240 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.gapCheck_window_one_excludes in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem gapCheck_window_one_excludes (K q : ℕ) (hq : 0 < q)
    (hcert : (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (1 + r) * 2 ^ (K - r)) % 2 ^ K))
        % 2 ^ K + q * (1 + K + 2) < 2 ^ K) :
    ∀ a : ℤ, (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) ≠ (a : ℝ) / (q : ℝ) := by
  sorry

/-- States prop:C2sup from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.gapFareyBound_window_1_240 in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gapFareyBound_window_1_240 (q : ℕ) (hq : 0 < q)
    (hqQ : q ≤ 79639646646701375323355774875831053) :
    (q * 1299094806818720335611738031537456208600423915562142231419225521361164904)
        % 2 ^ 240 + q * 243 < 2 ^ 240 := by
  sorry

/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_basePower_dilation in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_basePower_dilation {x : ℝ} (b₀ : ℕ)
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ n : ℕ, ∃ z : ℤ,
      0 < |((b₀ ^ n : ℕ) : ℝ) * x - (z : ℝ)| ∧ := by
  sorry

/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_product_tendsto_zero in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_of_den_mul_error_product_tendsto_zero
    {x : ℝ} {u : ℕ → ℚ} {ε : ℕ → ℝ}
    (hne : ∀ j, ((u j : ℚ) : ℝ) ≠ x)
    (herr : ∀ j, |x - ((u j : ℚ) : ℝ)| ≤ ε j)
    (h0 : Filter.Tendsto (fun j => ((u j).den : ℝ) * ε j) Filter.atTop (nhds 0)) :
    Irrational x := by
  sorry

/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_den_mul_error_tendsto_zero in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_of_den_mul_error_tendsto_zero {x : ℝ} {u : ℕ → ℚ}
    (hne : ∀ᶠ k in Filter.atTop, ((u k : ℚ) : ℝ) ≠ x)
    (h0 : Filter.Tendsto (fun k => ((u k).den : ℝ) * |x - ((u k : ℚ) : ℝ)|)
      Filter.atTop (nhds 0)) :
    Irrational x := by
  sorry

/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_dirichlet_gap in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem irrational_of_dirichlet_gap {x : ℝ}
    (h : ∀ Q : ℤ, 1 ≤ Q → ∃ m z : ℤ,
      0 < |(m : ℝ) * x - (z : ℝ)| ∧ |(m : ℝ) * x - (z : ℝ)| < 1 / (Q : ℝ)) :
    Irrational x := by
  sorry

/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_near_integer_base_powers in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_of_near_integer_base_powers (b₀ : ℕ) (hb : 2 ≤ b₀) {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ (n : ℕ) (z : ℤ),
      0 < |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| ∧ |(b₀ : ℝ) ^ n * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  sorry

/-- States catalogue:cert:d2 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_near_integer_multiples in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_of_near_integer_multiples {ξ : ℝ}
    (h : ∀ q : ℕ, 0 < q → ∃ m z : ℤ,
      0 < |(m : ℝ) * ξ - (z : ℝ)| ∧ |(m : ℝ) * ξ - (z : ℝ)| < 1 / (q : ℝ)) :
    Irrational ξ := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_of_unbounded_window_one_gapCheck in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_of_unbounded_window_one_gapCheck (g : ℕ → ℕ)
    (hg : Filter.Tendsto g Filter.atTop Filter.atTop)
    (hcheck : ∀ K q : ℕ, 0 < q → q ≤ g K →
      (q * ((∑ r ∈ Finset.Icc 1 K, Nat.totient (1 + r) * 2 ^ (K - r)) % 2 ^ K))
        % 2 ^ K + q * (1 + K + 2) < 2 ^ K) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States prop:transfer from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_block_cosine_gap in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_totientSeries_of_block_cosine_gap
    (hgap : ∀ h : ℕ, 1 ≤ h → ∀ X₀ : ℕ, ∃ X : ℕ, max X₀ 1 ≤ X ∧
      (∑ N ∈ Finset.Ico X (2 * X),
          Real.cos (2 * Real.pi *
            ((2 : ℝ) ^ N * ((2 : ℝ) ^ h - 1) *
              (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n))))
        ≤ (89 / 100 : ℝ) * X) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States prop:C2sup from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_fareyGapExclusionUnbounded
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem irrational_totientSeries_of_fareyGapExclusionUnbounded
    (hsup : FareyGapExclusionUnbounded) :
    Irrational (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.irrational_totientSeries_of_rational_separation in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem irrational_totientSeries_of_rational_separation (u : ℕ → ℚ)
    (hne : ∀ᶠ t in Filter.atTop,
      ((u t : ℝ)) ≠ ∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n)
    (h0 : Filter.Tendsto
      (fun t => ((u t).den : ℝ) * := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_orderConsumer_instance in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem mersenneLayer_orderConsumer_instance :
    BoundedDegreeOrderConsumer (fun n => 2 ^ n - 1) 1 1 ∧
      ∀ q p : ℕ, q.Prime → p.Prime → p ∣ 2 ^ q - 1 →
        orderOf ((p : ℕ) : ZMod q) = 1 ∧ orderOf ((2 : ℕ) : ZMod p) = q := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_prime_divisor_order
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem mersenneLayer_prime_divisor_order {q p : ℕ} (hq : q.Prime) (hp : p.Prime)
    (hdvd : p ∣ 2 ^ q - 1) :
    orderOf ((2 : ℕ) : ZMod p) = q ∧ q ∣ p - 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.mersenneLayer_unbounded_prime_support in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem mersenneLayer_unbounded_prime_support (B N₀ : ℕ) :
    ∃ q p : ℕ, q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ 2 ^ q - 1 ∧ B < p := by
  sorry

/-- States catalogue:mob:e1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.nine_tenths_lt_cos_pi_div_eight in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem nine_tenths_lt_cos_pi_div_eight : (9 / 10 : ℝ) < Real.cos (Real.pi / 8) := by
  sorry

/-- States catalogue:cert:d2, prop:D1D2-inv from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_le_abs_int_combination
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem one_div_den_le_abs_int_combination (p : ℚ) (m z : ℤ)
    (hne : (m : ℝ) * (p : ℝ) - (z : ℝ) ≠ 0) :
    (1 : ℝ) / (p.den : ℝ) ≤ |(m : ℝ) * (p : ℝ) - (z : ℝ)| := by
  sorry

/-- States prop:D1D2-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.one_div_den_mul_den_le_abs_diff in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem one_div_den_mul_den_le_abs_diff {x u : ℚ} (hne : x ≠ u) :
    (1 : ℝ) / ((x.den : ℝ) * (u.den : ℝ)) ≤ |(x : ℝ) - (u : ℝ)| := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_finite_prime_escape
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem orderConsumer_finite_prime_escape {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m) (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ S : Finset ℕ, ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      ∀ p ∈ S, p.Prime → ¬ p ∣ C (m * q) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_index_lt_pow in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem orderConsumer_index_lt_pow {C : ℕ → ℕ} {m d q p : ℕ}
    (horder : BoundedDegreeOrderConsumer C m d)
    (hq : q.Prime) (hp : p.Prime) (hpC : p ∣ C (m * q)) :
    m * q < p ^ d := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.orderConsumer_unbounded_prime_divisors in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem orderConsumer_unbounded_prime_divisors {C : ℕ → ℕ} {m d : ℕ}
    (hm : 1 ≤ m)
    (hlayer : ∃ Q₀ : ℕ, ∀ q : ℕ, q.Prime → Q₀ ≤ q →
      1 < C (m * q) ∧ Nat.Coprime (C (m * q)) (m * q))
    (horder : BoundedDegreeOrderConsumer C m d) :
    ∀ B N₀ : ℕ, ∃ q p : ℕ,
      q.Prime ∧ N₀ ≤ q ∧ p.Prime ∧ p ∣ C (m * q) ∧ B < p := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.orderOf_two_mod_seven in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem orderOf_two_mod_seven : orderOf ((2 : ℕ) : ZMod 7) = 3 := by
  sorry

/-- States prop:b7 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.parityComparisonProperties_do_not_imply_irrational
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem parityComparisonProperties_do_not_imply_irrational :
    ¬ ∀ c : ℕ → ℕ, ParityComparisonProperties c →
        Irrational (∑' n : ℕ, (c n : ℝ) / 2 ^ n) := by
  sorry

/-- States prop:C1-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.positive_antidiagonal_one in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem positive_antidiagonal_one :
    ((Finset.antidiagonal 1).filter
        fun q : ℕ × ℕ => 0 < q.1 ∧ 0 < q.2 ∧ Nat.Coprime q.1 q.2) = ∅ := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_formula in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem primeJumpSharpRadius_formula (H p L : ℕ) :
    primeJumpSharpRadius H p L = 3 * p * H + (p + 1) * (L + 2) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_lt_twoCellRadius in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem primeJumpSharpRadius_lt_twoCellRadius {H p L : ℕ} (hpH : 0 < p * H) :
    primeJumpSharpRadius H p L < (4 * p * H + (p + 1) * (L + 2) : ℤ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.primeJumpSharpRadius_saves_pH in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem primeJumpSharpRadius_saves_pH (H p L : ℕ) :
    (4 * p * H + (p + 1) * (L + 2) : ℤ) - primeJumpSharpRadius H p L = p * H := by
  sorry

/-- States prop:D9-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.rational_gap_lower_bound in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem rational_gap_lower_bound {lo hi : ℚ} (hlt : lo < hi) :
    (1 : ℝ) / ((hi.den : ℝ) * (lo.den : ℝ)) ≤ (hi : ℝ) - (lo : ℝ) := by
  sorry

/-- States prop:AR-03-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.rough_integer_prime_count_and_totient_bound in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem rough_integer_prime_count_and_totient_bound {a n : ℕ} (ha : 8 ≤ a)
    (hnPos : 0 < n) (hrough : ∀ r : ℕ, Nat.Prime r → r ∣ n → 2 ^ a < r)
    (hnPow : n < 2 ^ (2 * 2 ^ a)) :
    n.primeFactors.card < 2 ^ a / 4
      ∧ (3 / 4 : ℚ) * (n : ℚ) < (Nat.totient n : ℚ) := by
  sorry

/-- States prop:SK-01-inv from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.shortWindow_inequalities in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem shortWindow_inequalities :
    (23 : ℕ) < 2 * 2 ^ 4 ∧ (93 : ℕ) < 2 * 2 ^ 6 := by
  sorry

/-- States catalogue:mob:f1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_totient_ne_totient in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sum_divisors_totient_ne_totient :
    (∀ n : ℕ, ∑ d ∈ n.divisors, Nat.totient d = n) ∧
      (∑ d ∈ (2 : ℕ).divisors, Nat.totient d) = 2 ∧ Nat.totient 2 = 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.three_not_dvd_two_pow in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem three_not_dvd_two_pow (j : ℕ) : ¬ (3 ∣ 2 ^ j) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_concatenation in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totientBlock_concatenation (a b N : ℕ) :
    totientBlock (a + b) N = 2 ^ b * totientBlock a N + totientBlock b (N + a) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_doubling in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totientBlock_doubling (h N : ℕ) :
    totientBlock (2 * h) N = 2 ^ h * totientBlock h N + totientBlock h (N + h) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientBlock_eq_paper_indexed_sum
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem totientBlock_eq_paper_indexed_sum (a N : ℕ) :
    totientBlock a N
      = ∑ j ∈ Finset.Icc 1 a, (Nat.totient (N + j) : ℤ) * 2 ^ (a - j) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsAJ
