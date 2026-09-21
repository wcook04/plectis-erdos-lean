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
`Erdos249257.DiagonalFreshLossBridge`, `Erdos249257.FullTargetPrimeAdjunctionNoGo`,
`Erdos249257.MersenneShadowCyclotomicNoncollapse`,
`Erdos249257.MersenneShadowDenominatorGrowth`, `Erdos249257.RadicalMobiusShadow`,
`ErdosProblems.Erdos249.PaperCompleteR20.DenominatorBounds`,
`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel`,
`ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodelEndpoint`,
`ErdosProblems.Erdos249.PaperCompleteR20.GenericTailCertificates`,
`ErdosProblems.Erdos249.PaperCompleteR20.PeriodicIntegerAffine`,
`ErdosProblems.Erdos249.PaperCompleteR20.SignedDyadicClearing`,
`ErdosProblems.Erdos249.PaperCompleteR21.AffineDivisorAnnihilation`,
`ErdosProblems.Erdos249.PaperCompleteR21.DivisorChannelSplitAndSeamDoubling`,
`ErdosProblems.Erdos249.PaperCompleteR21.LambertDivisorTransform`,
`ErdosProblems.Erdos249.PaperCompleteR21.PhaseEnergyAndForeignResidueProjection`,
`ErdosProblems.Erdos249.PaperCompleteR21.PillaiGcdExpectation`,
`ErdosProblems.Erdos249.PaperCompleteR21.SquaredMersenneDivisorIdentities`,
`ErdosProblems.Erdos249.PaperCompleteR21.SternBrocotStoppingRecursion`,
`ErdosProblems.Erdos249.PaperCompleteR21.TemperedOrbitAndSquaredMersenneTail`,
`ErdosProblems.Erdos249.PaperCompleteR7.PeriodicAndPulse`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification249PaperStatementsAE

noncomputable def foreignChannelPhaseTerm (d H s : ℕ) : ℤ :=
  if d ∣ 2 * H + s then
    ArithmeticFunction.moebius d * ((((2 * H + s) / d : ℕ) : ℤ))
  else if d ∣ H + s then
    -(ArithmeticFunction.moebius d * ((((H + s) / d : ℕ) : ℤ)))
  else 0

noncomputable def mersenne (n : ℕ) : ℕ := 2 ^ n - 1

noncomputable def mobiusNumerator (r : ℕ) : ℤ :=
  ∑ s ∈ r.primeFactors.powerset,
    (-1 : ℤ) ^ s.card *
      ((r / s.prod id : ℕ) : ℤ) *
        (((mersenne r) / (mersenne (s.prod id)) : ℕ) : ℤ)

noncomputable def baseMobiusShadow (r : ℕ) : ℚ :=
  Rat.divInt (mobiusNumerator r) (mersenne r : ℤ)

noncomputable def squarefreeKernel (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

noncomputable def numericMobiusShadow (H : ℕ) : ℚ :=
  baseMobiusShadow (squarefreeKernel H) / (squarefreeKernel H : ℚ)

noncomputable def scaleExplicitShadowRat (H : ℕ) : ℚ :=
  (H : ℚ) * numericMobiusShadow H

noncomputable def scaleExplicitShadow (H : ℕ) : ℝ :=
  (scaleExplicitShadowRat H : ℝ)

noncomputable def lcmHeight (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).lcm (fun n ↦ n)

noncomputable def upperHalfPrimes (t : ℕ) : Finset ℕ :=
  (Finset.Ioc (t / 2) t).filter Nat.Prime

noncomputable def dyadicBase (B : ℕ) : ℚ :=
  2 - ∑ n ∈ Finset.range (B + 1), ((n - Nat.totient n : ℕ) : ℚ) / 2 ^ n

noncomputable def gamma (B P n : ℕ) : ℕ :=
  if n ≤ B then Nat.totient n else if P ∣ n then n - 1 else n

noncomputable def discrepancy (c : ℕ → ℕ) (h N L : ℕ) : ℤ :=
  ∑ j ∈ Finset.range L,
    ((c (N + h + j + 1) : ℤ) - c (N + j + 1)) * 2 ^ (L - 1 - j)

noncomputable def certificate (c : ℕ → ℕ) (h N L : ℕ) : Prop :=
  (N + h + L + 2 : ℤ) < discrepancy c h N L % 2 ^ L ∧
  discrepancy c h N L % 2 ^ L < 2 ^ L - (N + h + L + 2)

noncomputable def separation (c : ℕ → ℕ) : Prop :=
  ∀ h : ℕ, 0 < h → ∀ N₀ : ℕ, ∃ N, N₀ ≤ N ∧ ∃ L, certificate c h N L

noncomputable def value (B P : ℕ) : ℚ := dyadicBase B - 1 / ((2 ^ P - 1 : ℕ) : ℚ)

noncomputable def integerAffineValue {ι : Type*} (a : ι → ℕ) (b : ι → ℤ)
    (i : ι) (n : ℕ) : ℕ :=
  Int.toNat ((a i : ℤ) * (n : ℤ) + b i)

noncomputable def complementSummand (d H s : ℕ) : ℚ :=
  (ArithmeticFunction.moebius d : ℚ) *
    (((2 * H + s : ℕ) : ℚ) / (d : ℚ) * (if d ∣ 2 * H + s then 1 else 0) -
      ((H + s : ℕ) : ℚ) / (d : ℚ) * (if d ∣ H + s then 1 else 0))

noncomputable def lambertValue (f : ℕ → ℝ) : ℝ :=
  ∑' n : ℕ+, f (n : ℕ) / ((2 : ℝ) ^ (n : ℕ) - 1)

noncomputable def mobiusTermKernel (d N : ℕ) : ℝ :=
  (N : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)) + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2)

noncomputable def pillaiP (n : ℕ) : ℕ := ∑ e ∈ n.divisors, Nat.totient e * (n / e)

noncomputable def totientArith : ArithmeticFunction ℕ := ⟨Nat.totient, Nat.totient_zero⟩

/-- States catalogue:mob:b6 from the long record for Erdős problem #249. Transported from
Erdos249257.MersenneShadowCyclotomicNoncollapse.lcmHeight_upperHalf_product_dvd_den in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem lcmHeight_upperHalf_product_dvd_den
    {t : ℕ} (ht : 5 ≤ t) :
    (∏ p ∈ upperHalfPrimes t, mersenne p) ∣
      ((lcmHeight t : ℚ) *
        numericMobiusShadow (lcmHeight t)).den := by
  sorry

/-- States catalogue:mob:b6 from the long record for Erdős problem #249. Transported from
Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfChannel_product_dvd_den_of_coprime_scale
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem upperHalfChannel_product_dvd_den_of_coprime_scale
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hscale : Nat.Coprime
      (∏ p ∈ P, mersenne p) h) :
    (∏ p ∈ P, mersenne p) ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := by
  sorry

/-- States catalogue:mob:b6 from the long record for Erdős problem #249. Transported from
Erdos249257.MersenneShadowCyclotomicNoncollapse.upperHalfChannel_product_dvd_den_of_scale_primeFactors_le
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem upperHalfChannel_product_dvd_den_of_scale_primeFactors_le
    (P : Finset ℕ) {t r h : ℕ} (ht : 5 ≤ t) (hr : Squarefree r)
    (hprime : ∀ p ∈ P, p.Prime) (hpr : ∀ p ∈ P, p ∣ r)
    (hupper : ∀ p ∈ P, t < 2 * p)
    (hcut : ∀ q : ℕ, q.Prime → q ∣ r → q ≤ t)
    (hhcut : ∀ q : ℕ, q.Prime → q ∣ h → q ≤ t) :
    (∏ p ∈ P, mersenne p) ∣
      (Rat.divInt ((h : ℤ) * mobiusNumerator r)
        (mersenne r : ℤ)).den := by
  sorry

/-- States catalogue:mob:b7b from the long record for Erdős problem #249. Transported from
Erdos249257.MersenneShadowDenominatorGrowth.lcmHeight_five_scaledMobiusShadow_den_exact in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem lcmHeight_five_scaledMobiusShadow_den_exact :
    ((lcmHeight 5 : ℚ) *
        numericMobiusShadow (lcmHeight 5)).den =
      mersenne 30 / 3 := by
  sorry

/-- States thm:gamma from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.discrepancy_prefix in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem discrepancy_prefix (B P h N L : ℕ) (hB : N + h + L ≤ B) :
    discrepancy (gamma B P) h N L =
      discrepancy Nat.totient h N L := by
  sorry

/-- States thm:gamma from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.exact_denominator in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem exact_denominator (B P : ℕ) (hBP : B < P) :
    ∃ e ≤ B, (value B P).den = 2 ^ e * (2 ^ P - 1) := by
  sorry

/-- States thm:gamma from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_le in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem gamma_le (B P n : ℕ) : gamma B P n ≤ n := by
  sorry

/-- States cor:b1, thm:gamma from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_not_separation in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem gamma_not_separation (B P : ℕ) (hBP : B < P) : ¬ separation (gamma B P) := by
  sorry

/-- States thm:gamma from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.gamma_prefix in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem gamma_prefix (B P n : ℕ) (hn : n ≤ B) : gamma B P n = Nat.totient n := by
  sorry

/-- States thm:gamma from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_certificate_after_prefix
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem no_certificate_after_prefix (B P : ℕ) (hBP : B < P) :
    ∀ N : ℕ, B ≤ N → ∀ L : ℕ, ¬ certificate (gamma B P) P N L := by
  sorry

/-- States cor:b1 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.FinitePrefixCountermodel.no_uniform_prefix_rule in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem no_uniform_prefix_rule (B : ℕ) :
    ¬ (∀ c : ℕ → ℕ, (∀ n, c n ≤ n) → (∀ n, n ≤ B → c n = Nat.totient n) → separation c) := by
  sorry

/-- States cor:periodic-freezing from the short record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.periodic_freezing_integer_affine in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem periodic_freezing_integer_affine
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℕ) (b : ι → ℤ) (ha : ∀ i, 0 < a i)
    (hcross : ∀ i j, i ≠ j → (a i : ℤ) * b j ≠ (a j : ℤ) * b i)
    (w : ι → ℕ → ℚ)
    (hperiodic : ∀ i, ∃ q : ℕ, 0 < q ∧ ∀ n, w i (n + q) = w i n)
    (hrel : ∃ N₀, ∀ n, N₀ ≤ n →
      ∑ i, w i n * (Nat.totient (integerAffineValue a b i n) : ℚ) = 0) :
    ∀ i n, w i n = 0 := by
  sorry

/-- States catalogue:mob:d3 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_clearing in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem signed_dyadic_clearing {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α)
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (2 : ℚ) ^ e m * (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) =
      ((∑ i ∈ s, u i * (2 : ℤ) ^ (e m - e i) : ℤ) : ℚ) := by
  sorry

/-- States catalogue:mob:d3 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.signed_dyadic_sum_ne_zero in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem signed_dyadic_sum_ne_zero {α : Type*} (s : Finset α)
    (u : α → ℤ) (e : α → ℕ) (m : α) (hm : m ∈ s)
    (hu : ¬ Even (u m))
    (hmax : ∀ i ∈ s, i ≠ m → e i < e m) :
    (∑ i ∈ s, (u i : ℚ) / 2 ^ e i) ≠ 0 := by
  sorry

/-- States catalogue:mob:b7a from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR20.upper_half_product_denominator_bounds in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem upper_half_product_denominator_bounds {t : ℕ} (ht : 5 ≤ t) :
    2 ^ (t / 2) ≤ (∏ p ∈ upperHalfPrimes t, mersenne p) ∧
    (∏ p ∈ upperHalfPrimes t, mersenne p) ≤
      ((lcmHeight t : ℚ) * numericMobiusShadow (lcmHeight t)).den := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_mobiusSquareTail_le_paper in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem abs_mobiusSquareTail_le_paper (D : ℕ) : := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.abs_moebius_cast_le_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem abs_moebius_cast_le_one (d : ℕ) : := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.boundary_pair_at_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem boundary_pair_at_one :
    (1, 0) ∈ (Finset.antidiagonal 1).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2) ∧
      ((Finset.antidiagonal 1).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2)).card = 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.card_coprime_antidiagonal in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem card_coprime_antidiagonal (n : ℕ) :
    ((Finset.antidiagonal n).filter
        (fun p : ℕ × ℕ => 0 < p.1 ∧ Nat.Coprime p.1 p.2)).card = Nat.totient n := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.card_mul_sq_le_pairwise_energy in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem card_mul_sq_le_pairwise_energy {α : Type*} [DecidableEq α]
    (T : Finset α) (z : α → ℂ) (P : Finset (α × α)) (δ : ℝ)
    (hP : P ⊆ T.product T) (hδ : 0 ≤ δ)
    (hsep : ∀ p ∈ P, δ ≤ ‖z p.1 - z p.2‖) :
    (P.card : ℝ) * δ ^ 2 ≤ ∑ i ∈ T, ∑ j ∈ T, ‖z i - z j‖ ^ 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_eq_phaseTerm in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem complementSummand_eq_phaseTerm {d H s : ℕ} (hd : 0 < d) (hdH : ¬d ∣ H) :
    complementSummand d H s = ((foreignChannelPhaseTerm d H s : ℤ) : ℚ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.complementSummand_low_double_echo
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem complementSummand_low_double_echo {d H s : ℕ} (_hH : 0 < H) (_hd : 0 < d)
    (hdH : ¬d ∣ H) (hLow : d ∣ H + s) :
    complementSummand d H s =
        -((ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ)) ∧
      complementSummand d H (2 * s) =
        2 * ((ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ)) ∧
      (d ∣ 2 * H + 2 * s ∧ ¬d ∣ H + 2 * s) ∧
      complementSummand d H (2 * s) = -2 * complementSummand d H s := by
  sorry

/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.divisibility_mass in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem divisibility_mass (a : ℕ) (ha : 0 < a) :
    (∑' k : ℕ, if 0 < k ∧ a ∣ k then ((1 : ℝ) / 2) ^ k else 0)
      = 1 / ((2 : ℝ) ^ a - 1) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.divisorIndex_endpoint_behaviour in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem divisorIndex_endpoint_behaviour {d H s : ℕ} (hdH : d ∣ H) :
    (d ∣ 2 * H + s ↔ d ∣ s) ∧ (d ∣ H + s ↔ d ∣ s) ∧
      (ArithmeticFunction.moebius d : ℚ) * ((2 * H + s : ℕ) : ℚ) / (d : ℚ) -
          (ArithmeticFunction.moebius d : ℚ) * ((H + s : ℕ) : ℚ) / (d : ℚ) =
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.doubling_tempered_sequence_eq_zero
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem doubling_tempered_sequence_eq_zero
    (d : ℕ → ℝ) (hrec : ∀ N : ℕ, d (N + 1) = 2 * d N)
    (hlittleO :
      Filter.Tendsto (fun N : ℕ ↦ d N / (2 : ℝ) ^ N) Filter.atTop (nhds 0)) :
    ∀ N : ℕ, d N = 0 := by
  sorry

/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.gcd_moment_identity_three_members
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem gcd_moment_identity_three_members :
    (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' n : ℕ+, (((pillaiP (n : ℕ) : ℕ) : ℝ) - ((n : ℕ) : ℝ))
            * ((1 : ℝ) / 2) ^ (n : ℕ))
      ∧ (∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2
        = ∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
            then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0) := by
  sorry

/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.joint35_coefficient_moments in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_coefficient_moments :
    ((4 : ℝ) + (-3) + (-2) + 1 = 0)
      ∧ ((4 : ℝ) * 1 + (-3) * 3 + (-2) * 5 + 1 * 15 = 0)
      ∧ ((4 : ℝ) * 1 ^ 2 + (-3) * 3 ^ 2 + (-2) * 5 ^ 2 + 1 * 15 ^ 2 = 152)
      ∧ ((1 : ℝ) * 1 - 3 * 1 - 2 * 1 + 4 = 0)
      ∧ ((3 : ℝ) * 5 - 3 * 3 - 2 * 5 + 4 = 0)
      ∧ ((9 : ℝ) * 25 - 3 * 9 - 2 * 25 + 4 = 152) := by
  sorry

/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.joint35_mobiusTermKernel_zero in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem joint35_mobiusTermKernel_zero (d H : ℕ) :
    mobiusTermKernel d (15 * H) - 3 * mobiusTermKernel d (3 * H)
      - 2 * mobiusTermKernel d (5 * H) + 4 * mobiusTermKernel d H = 0 := by
  sorry

/-- States catalogue:cert:d7 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.lambertValue_eq_divisor_sum_series in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem lambertValue_eq_divisor_sum_series (f : ℕ → ℝ)
    (hf : Summable (fun p : ℕ+ × ℕ+ =>
      f (p.1 : ℕ) * ((1 : ℝ) / 2) ^ ((p.1 : ℕ) * (p.2 : ℕ)))) :
    lambertValue f
      = ∑' m : ℕ+, (∑ e ∈ (m : ℕ).divisors, f e) * ((1 : ℝ) / 2) ^ (m : ℕ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.mersenne_geometric_shift in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem mersenne_geometric_shift (D j : ℕ) :
    (2 : ℝ) ^ j * ((2 : ℝ) ^ (D + 1) - 1) ≤ (2 : ℝ) ^ (D + 1 + j) - 1 := by
  sorry

/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_affine_in_multiplier in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem mobiusTermKernel_affine_in_multiplier (d H m : ℕ) :
    mobiusTermKernel d (m * H)
      = (m : ℝ) * ((H : ℝ) / ((d : ℝ) * ((2 : ℝ) ^ d - 1)))
        + (2 : ℝ) ^ d / (((2 : ℝ) ^ d - 1) ^ 2) := by
  sorry

/-- States catalogue:mob:e3 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.mobiusTermKernel_moment_annihilation in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem mobiusTermKernel_moment_annihilation
    {ι : Type*} [Fintype ι] (c : ι → ℝ) (m : ι → ℕ) (d H : ℕ)
    (hzero : ∑ i, c i = 0) (hfirst : ∑ i, c i * (m i : ℝ) = 0) :
    ∑ i, c i * mobiusTermKernel d (m i * H) = 0 := by
  sorry

/-- States catalogue:mob:a7 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.pair_divisibility_mass in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem pair_divisibility_mass (d : ℕ) (hd : 0 < d) :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2 ∧ d ∣ p.1 ∧ d ∣ p.2
        then ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = 1 / ((2 : ℝ) ^ d - 1) ^ 2 := by
  sorry

/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.pillaiP_eq_totient_mul_id in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem pillaiP_eq_totient_mul_id (n : ℕ) :
    (totientArith * ArithmeticFunction.id) n = pillaiP n := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.scaleExplicitShadow_eq_divisorChannels in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem scaleExplicitShadow_eq_divisorChannels {H : ℕ} (hH : 0 < H) :
    scaleExplicitShadow H =
      (H : ℝ) *
        ∑ d ∈ H.divisors,
          ((ArithmeticFunction.moebius d : ℤ) : ℝ) /
            ((d : ℝ) * ((2 : ℝ) ^ d - 1)) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.squarefreeKernel_eq_prod_primeFactors in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem squarefreeKernel_eq_prod_primeFactors (H : ℕ) :
    squarefreeKernel H = ∏ p ∈ H.primeFactors, p := by
  sorry

/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.stopping_probability_ge_third in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem stopping_probability_ge_third (a b : ℕ+) :
    (1 : ℝ) / 3 ≤ ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
      / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) := by
  sorry

/-- States catalogue:mob:a9a from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.stopping_transition_probabilities_sum_one in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem stopping_transition_probabilities_sum_one (a b : ℕ+) :
    ((2 : ℝ) ^ (a : ℕ) - 1) * ((2 : ℝ) ^ (b : ℕ) - 1)
        / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (a : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1)
      + ((2 : ℝ) ^ (b : ℕ) - 1) / ((2 : ℝ) ^ ((a : ℕ) + (b : ℕ)) - 1) = 1 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_divisorIndices_mobius in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem sum_divisorIndices_mobius (H s : ℕ) (hH : 0 < H) :
    ∑ d ∈ {d ∈ H.divisors | d ∣ s},
        (ArithmeticFunction.moebius d : ℚ) * (H : ℚ) / (d : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.sum_divisors_moebius_div_eq_totient_div in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem sum_divisors_moebius_div_eq_totient_div {g : ℕ} (hg : 0 < g) :
    ∑ d ∈ g.divisors, (ArithmeticFunction.moebius d : ℚ) / (d : ℚ) =
      (Nat.totient g : ℚ) / (g : ℚ) := by
  sorry

/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.sum_gcd_Icc_eq_pillaiP in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem sum_gcd_Icc_eq_pillaiP (n : ℕ) (hn : 0 < n) :
    ∑ k ∈ Finset.Icc 1 n, Nat.gcd k n = pillaiP n := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_doubling_seam in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totientDifference_doubling_seam (H r : ℕ) (hH : Even H) :
    (Even r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          2 * ((Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ))) ∧
      (Odd r →
        (Nat.totient (4 * H + 2 * r) : ℤ) - (Nat.totient (2 * H + 2 * r) : ℤ) =
          (Nat.totient (2 * H + r) : ℤ) - (Nat.totient (H + r) : ℤ)) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totientDifference_eq_divisorPart_add_complement in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totientDifference_eq_divisorPart_add_complement (H s : ℕ) (hH : 0 < H) :
    (Nat.totient (2 * H + s) : ℚ) - (Nat.totient (H + s) : ℚ) =
      (H : ℚ) * (Nat.totient (Nat.gcd H s) : ℚ) / (Nat.gcd H s : ℚ) +
        ∑ d ∈ {d ∈ Finset.Icc 1 (2 * H + s) | ¬d ∣ H}, complementSummand d H s := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_eq_half_add_moebius_sq in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totientSeries_eq_half_add_moebius_sq :
    (∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ)) =
      1 / 2 +
        ∑' d : ℕ+,
          ((ArithmeticFunction.moebius (d : ℕ) : ℤ) : ℝ) /
            (((2 : ℝ) ^ (d : ℕ) - 1) ^ 2) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.totientSeries_pnat_form in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totientSeries_pnat_form :
    (∑' n : ℕ, (Nat.totient n : ℝ) / 2 ^ n) =
      ∑' n : ℕ+, (Nat.totient (n : ℕ) : ℝ) * ((1 : ℝ) / 2) ^ (n : ℕ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_eq_mobius_divisor_sum in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totient_eq_mobius_divisor_sum (n : ℕ) (hn : 0 < n) :
    (Nat.totient n : ℤ) =
      ∑ d ∈ n.divisors, ArithmeticFunction.moebius d * ((n / d : ℕ) : ℤ) := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_even in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totient_two_mul_even {n : ℕ} (hn : Even n) :
    Nat.totient (2 * n) = 2 * Nat.totient n := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.totient_two_mul_odd in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem totient_two_mul_odd {n : ℕ} (hn : Odd n) :
    Nat.totient (2 * n) = Nat.totient n := by
  sorry

/-- States catalogue:mob:a7 from the long record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR21.tsum_geometric_multiples in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem tsum_geometric_multiples (d : ℕ) (hd : 0 < d) :
    ∑' k : ℕ, ((1 : ℝ) / 2) ^ (d * (k + 1)) = 1 / ((2 : ℝ) ^ d - 1) := by
  sorry

/-- States catalogue:mob:a5, prop:pillai from the long record for Erdős problem #249.
Transported from
ErdosProblems.Erdos249.PaperCompleteR21.tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tsum_pos_pair_gcd_half_eq_totient_div_mersenne_sq :
    (∑' p : ℕ × ℕ, if 0 < p.1 ∧ 0 < p.2
        then (Nat.gcd p.1 p.2 : ℝ) * ((1 : ℝ) / 2) ^ (p.1 + p.2) else 0)
      = ∑' d : ℕ+, (Nat.totient (d : ℕ) : ℝ) / ((2 : ℝ) ^ (d : ℕ) - 1) ^ 2 := by
  sorry

/-- States the paper statement it is bound to from the long record for Erdős problem #249.
Transported from ErdosProblems.Erdos249.PaperCompleteR21.tsum_quarter_geometric in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem tsum_quarter_geometric : ∑' j : ℕ, ((1 : ℝ) / 4) ^ j = 4 / 3 := by
  sorry

/-- States lem:bounded-pulse from the short record for Erdős problem #249. Transported from
ErdosProblems.Erdos249.PaperCompleteR7.bounded_isolated_pulse in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem bounded_isolated_pulse
    (a : ℕ → ℤ) (C : ℝ) (hC : ∀ n, |(a n : ℝ)| ≤ C)
    (hpulse : ∀ L₀ : ℕ, ∃ L N : ℕ, L₀ ≤ L ∧ L < N ∧ a N ≠ 0 ∧
      ∀ j, 0 < j → j ≤ L → a (N - j) = 0 ∧ a (N + j) = 0) :
    Irrational (∑' n : ℕ, (a (n + 1) : ℝ) / 2 ^ (n + 1)) := by
  sorry

end Erdos249257.ExternalVerification249PaperStatementsAE
