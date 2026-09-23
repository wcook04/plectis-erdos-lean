/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/

import Mathlib

set_option autoImplicit false

/-!
# Erdős #1049, the Archimedean cap, Bezout Plucker jets and Hermite Pade no go families

Each theorem below restates, against Mathlib alone, a theorem of the Lean development
for Erdős problem #1049, in the order the papers state them. The definitions a statement
uses are copied in, and each declaration's documentation names the paper statement and
the source declaration it comes from. Erdős problem #1049 remains open, and no theorem
in this entry decides it.
-/

open Filter Asymptotics
open scoped Topology
open scoped BigOperators
open Filter

namespace PalomarCorpus.E1049.ArchimedeanCap
open Filter Asymptotics
open scoped Topology
/-- The declared clearing width of the n-th approximation pair: the larger of the degrees of the polynomials U n and V n, as a natural number. Under the Mathlib convention the zero polynomial has degree zero. -/
noncomputable def width (U V : ℕ → Polynomial ℤ) (n : ℕ) : ℕ := max (U n).natDegree (V n).natDegree
/-- The l^1 coefficient norm of an integer polynomial, the sum over its support of the absolute values of its coefficients, returned as a real number; the zero polynomial has empty support and height 0. -/
noncomputable def height (P : Polynomial ℤ) : ℝ := ∑ i ∈ P.support, |(P.coeff i : ℝ)|
/-- The remainder U_n(x) F(x) - V_n(x) of the n-th pair at the real point x, the polynomials being evaluated through the canonical ring map from the integers to the reals. Here F is an arbitrary real function supplied as a parameter rather than a fixed Lambert series. -/
noncomputable def remainder (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (x : ℝ) (n : ℕ) : ℝ :=
  (U n).eval₂ (Int.castRingHom ℝ) x * F x - (V n).eval₂ (Int.castRingHom ℝ) x
/-- Archimedean cap. Let U, V be sequences of integer polynomials, F any real function, and fix sigma > 0, delta > 0, h >= 0 not depending on the evaluation point. Assume for each eps > 0 that the width is eventually at most (delta + eps) n^2 and the logarithm of the larger l^1 coefficient norm eventually at most (h + eps) n^2; that at each real x > 1 the remainder is eventually nonzero; and that at each real x > 1 the quantity log |remainder| + sigma n^2 log x is o(n^2). Then sigma/(sigma + delta) <= 1/2, and for all naturals 1 <= b < a with log b / log a < sigma/(sigma + delta) the forms b^(width n) times the remainder at a/b tend to zero. -/
theorem archimedean_cap (U V : ℕ → Polynomial ℤ) (F : ℝ → ℝ) (σ δ h : ℝ)
    (hσ : 0 < σ) (hδ : 0 < δ) (hh : 0 ≤ h)
    (hdeg : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, (width U V n : ℝ) ≤ (δ + ε) * (n : ℝ)^2)
    (hheight : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
      Real.log (max (height (U n)) (height (V n))) ≤ (h + ε) * (n : ℝ)^2)
    (hne : ∀ x : ℝ, 1 < x → ∀ᶠ n in atTop, remainder U V F x n ≠ 0)
    (hrate : ∀ x : ℝ, 1 < x →
      (fun n => Real.log |remainder U V F x n| - (-σ * Real.log x) * (n : ℝ)^2)
        =o[atTop] (fun n : ℕ => (n : ℝ)^2)) :
    σ / (σ + δ) ≤ (1 : ℝ) / 2 ∧
    ∀ a b : ℕ, 1 ≤ b → b < a →
      Real.log b / Real.log a < σ / (σ + δ) →
      Tendsto (fun n => (b : ℝ) ^ width U V n * remainder U V F ((a : ℝ) / b) n)
        atTop (𝓝 0) := by
  sorry
end PalomarCorpus.E1049.ArchimedeanCap

namespace PalomarCorpus.E1049.BezoutPluckerJets
open scoped BigOperators
/-- Let w be a family of pairs in a commutative ring R, indexed by any type, and let a and b in R be coprime in the Bezout sense. If the anchor minor a (w i).2 - b (w i).1 vanishes for every index i, then every pairwise minor (w i).1 (w j).2 - (w i).2 (w j).1 vanishes: the whole family lies on the single line cut out by the anchor. -/
theorem anchor_det_zero_forces_all_det_zero {R : Type*} [CommRing R]
    {ι : Type*} (w : ι → R × R) {a b : R}
    (hab : IsCoprime a b) (hdet : ∀ i, a * (w i).2 - b * (w i).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  sorry
/-- Under the hypotheses above with R and the index type both finite, if the cardinality of R is smaller than 2 raised to the number of indices, then two distinct Boolean selectors have the same selected row sum in R times R. The minor collapse confines the selector sums to one copy of R, so the collision threshold is the cardinality of R rather than its square. -/
theorem binary_row_collision_of_anchor_det_zero
    {R ι : Type*} [CommRing R] [Fintype R] [Fintype ι]
    (w : ι → R × R) {a b : R}
    (hab : IsCoprime a b) (hdet : ∀ i, a * (w i).2 - b * (w i).1 = 0)
    (hcard : Fintype.card R < 2 ^ Fintype.card ι) :
    ∃ s t : ι → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry
/-- For a sequence of pairs in a commutative ring whose second coordinates are all units, vanishing of every adjacent minor implies vanishing of every pairwise minor. This is the sequential form of the previous propagation, with a unit coordinate in place of the coprime anchor. -/
theorem adjacent_det_zero_forces_all_det_zero {R : Type*} [CommRing R]
    (w : ℕ → R × R) (hunit : ∀ n, IsUnit (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0) :
    ∀ i j, (w i).1 * (w j).2 - (w i).2 * (w j).1 = 0 := by
  sorry
/-- At the modulus 2^S 3^R with R > 0, let w be a sequence of pairs of residues whose second coordinates are units and whose adjacent minors all vanish. Then for every k >= S + 2R there are two distinct Boolean selectors on k indices with equal selected row sums. The collapse halves the ambient two-coordinate threshold 2S + 4R to S + 2R. The vanishing of every adjacent minor is a hypothesis and is not established here for any actual approximation family. -/
theorem zmod_binary_tail_collision_of_two_three_depth {R S k : ℕ}
    [NeZero (2 ^ S * 3 ^ R)]
    (w : ℕ → ZMod (2 ^ S * 3 ^ R) × ZMod (2 ^ S * 3 ^ R))
    (hunit : ∀ n, IsUnit (w n).2)
    (hadj : ∀ n, (w n).1 * (w (n + 1)).2 - (w n).2 * (w (n + 1)).1 = 0)
    (hR : 0 < R) (hrank : S + 2 * R ≤ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry
end PalomarCorpus.E1049.BezoutPluckerJets

namespace PalomarCorpus.E1049.HermitePadeNoGo
/-- The decay exponent (1 + rho^2)/2 + sigma of that model: the normalised rate at which the remainder of the two-function approximation shrinks, in the two real parameters rho and sigma. Reading rho as the rectangularity parameter of the multi-index and sigma as the degree parameter is an interpretation; the statements below use only the formula and the admissible region rho >= 0, sigma >= 1 + rho. -/
noncomputable def hpDecay (rho sigma : ℝ) : ℝ :=
  (1 + rho ^ 2) / 2 + sigma
/-- The height exponent (1 + rho)^2/2 + sigma (1 + rho) of that model: the normalised logarithmic cost of clearing denominators, at the same parameters rho and sigma. -/
noncomputable def hpHeight (rho sigma : ℝ) : ℝ :=
  (1 + rho) ^ 2 / 2 + sigma * (1 + rho)
/-- The cyclotomic saving exponent 3 sigma^2 / pi^2 of the rectangular two-function Hermite-Pade exponent model: the normalised logarithmic size of the common cyclotomic factor removable from a pair of approximation polynomials at model parameter sigma, the constant 3/pi^2 being the mean density in the summatory totient estimate. Reading sigma as a degree parameter is an interpretation, and no statement here uses it. -/
noncomputable def hpCyclotomicSaving (sigma : ℝ) : ℝ :=
  3 * sigma ^ 2 / Real.pi ^ 2
/-- Rational-base height threshold associated with the explicit exponent model above. Local copy of ErdosProblems.Erdos1049.hpThreshold, restated so the compared statements elaborate against Mathlib alone. -/
noncomputable def hpThreshold (rho sigma : ℝ) : ℝ :=
  (hpDecay rho sigma - hpCyclotomicSaving sigma) /
    (hpHeight rho sigma + hpDecay rho sigma)
/-- The denominator-cleared comparison functional (pi^2 + 2) hpDecay - 6 sigma^2 - (pi^2 - 2) hpHeight, whose sign decides whether the rectangular two-function threshold of the model exceeds the classical one-function threshold 1/2 - 1/pi^2. -/
noncomputable def hpClearedGap (rho sigma : ℝ) : ℝ :=
  (Real.pi ^ 2 + 2) * hpDecay rho sigma - 6 * sigma ^ 2 -
    (Real.pi ^ 2 - 2) * hpHeight rho sigma
/-- Exact polynomial identity after the substitution sigma = 1 + rho + u: the cleared gap equals -pi^2 rho^2 - pi^2 rho u - 2 pi^2 rho - 2 rho^2 - 10 rho u - 4 rho - 6 u^2 - 8 u. The identity holds for all real rho and u; on rho >= 0 and u >= 0 every term is nonpositive. Supporting identity for the two comparison theorems below. -/
theorem hpClearedGap_expansion (rho u : ℝ) :
    hpClearedGap rho (1 + rho + u) =
      -Real.pi ^ 2 * rho ^ 2 - Real.pi ^ 2 * rho * u -
        2 * Real.pi ^ 2 * rho - 2 * rho ^ 2 - 10 * rho * u -
        4 * rho - 6 * u ^ 2 - 8 * u := by
  sorry
/-- On the admissible region rho >= 0 and sigma >= 1 + rho the cleared comparison functional is nonpositive. Supporting lemma for the threshold comparison. -/
theorem hpClearedGap_nonpos (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma ≤ 0 := by
  sorry
/-- On that same admissible region the cleared comparison functional vanishes if and only if rho = 0 and sigma = 1, the classical one-function endpoint. Supporting lemma for the sharpness statement. -/
theorem hpClearedGap_eq_zero_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpClearedGap rho sigma = 0 ↔ rho = 0 ∧ sigma = 1 := by
  sorry
/-- Over the whole admissible cone rho >= 0 and sigma >= 1 + rho, the rectangular two-function threshold of this explicit exponent model is at most 1/2 - 1/pi^2 = 0.398678816..., the classical one-function value. No admissible choice of exponents in the model improves on the classical threshold. The theorem is about this exponent model only: it constructs no approximants and proves no irrationality statement. -/
theorem rectangular_hp_threshold_le_classical (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma ≤ 1 / 2 - 1 / Real.pi ^ 2 := by
  sorry
/-- On the same cone the threshold equals 1/2 - 1/pi^2 if and only if rho = 0 and sigma = 1. The previous bound is therefore sharp and its equality locus is that single point. -/
theorem rectangular_hp_threshold_eq_classical_iff (rho sigma : ℝ)
    (hrho : 0 ≤ rho) (hsigma : 1 + rho ≤ sigma) :
    hpThreshold rho sigma = 1 / 2 - 1 / Real.pi ^ 2 ↔
      rho = 0 ∧ sigma = 1 := by
  sorry
end PalomarCorpus.E1049.HermitePadeNoGo

namespace PalomarCorpus.E1049.PrimeSupportSelectors
open Filter
/-- At a rational target a/q with q > 0, two integral rows whose exterior determinant A_1 B_2 - A_2 B_1 is nonzero cannot both have remainder below 1/q: at least one of |B_1 (a/q) - A_1| and |B_2 (a/q) - A_2| is at least 1/q. Nonvanishing of the determinant is the only hypothesis on the rows; no primality, no denominator support condition and no coprimality of a and q is assumed. -/
theorem twoSelector_rationalGap
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hdet : A₁ * B₂ - A₂ * B₁ ≠ 0) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  sorry
/-- At a rational target a/q with q > 0, an integral linear form B (a/q) - A that does not vanish has absolute value at least 1/q. Nonvanishing of the form is the only hypothesis; no primality, no denominator support condition and no coprimality of a and q is assumed. -/
theorem integerLinearForm_rationalGap
    (a q A B : ℤ) (hq : 0 < q)
    (hne : (B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ) ≠ 0) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry
/-- For sequences of integral rows whose exterior determinant is nonzero at every index, the two real linear forms B_1 (a/q) - A_1 and B_2 (a/q) - A_2 cannot both tend to zero at a rational target a/q with q > 0. No such pair of selectors jointly witnesses vanishing at a rational point. -/
theorem rationalTwoSelector_notBothTendstoZero
    (a q : ℤ) (hq : 0 < q)
    (A₁ B₁ A₂ B₂ : ℕ → ℤ)
    (hdet : ∀ n, A₁ n * B₂ n - A₂ n * B₁ n ≠ 0) :
    ¬(Tendsto
        (fun n ↦ (B₁ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ n : ℝ))
        atTop (nhds 0) ∧
      Tendsto
        (fun n ↦ (B₂ n : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ n : ℝ))
        atTop (nhds 0)) := by
  sorry
/-- If two real linear forms at a common real target F have remainders |B_1 F - A_1| and |B_2 F - A_2| at most eps, then their exterior determinant satisfies |A_1 B_2 - A_2 B_1| <= eps (|B_1| + |B_2|), so joint decay is paid for in determinant size. The statement is about real data and uses no change of basis, no integrality and no coefficient-height hypothesis. -/
theorem twoSelector_detHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ F ε : ℝ)
    (h₁ : |B₁ * F - A₁| ≤ ε) (h₂ : |B₂ * F - A₂| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤ ε * (|B₁| + |B₂|) := by
  sorry
/-- If a real two by two recombination with |u z - v w| = 1 and all four entries bounded in absolute value by H makes both recombined remainders at most eps >= 0 at a common real target F, then the original exterior determinant satisfies |A_1 B_2 - A_2 B_1| <= 2 H eps (|B_1| + |B_2|). Joint decay reached through a bounded change of basis is still paid for in determinant size; integer unimodular recombination is a special case. -/
theorem twoSelector_unimodularHeightDecay_tradeoff
    (A₁ B₁ A₂ B₂ u v w z F H ε : ℝ)
    (hunimod : |u * z - v * w| = 1)
    (hε : 0 ≤ ε)
    (hu : |u| ≤ H) (hv : |v| ≤ H) (hw : |w| ≤ H) (hz : |z| ≤ H)
    (h₁ : |(u * B₁ + v * B₂) * F - (u * A₁ + v * A₂)| ≤ ε)
    (h₂ : |(w * B₁ + z * B₂) * F - (w * A₁ + z * A₂)| ≤ ε) :
    |A₁ * B₂ - A₂ * B₁| ≤
      2 * H * ε * (|B₁| + |B₂|) := by
  sorry
/-- Let ell be prime, let q > 0 with ell not dividing q, let ell divide both B_1 and B_2, and let ell^2 not divide A_1 B_2 - A_2 B_1. Then at least one of the two rows has the full gap 1/q at the target a/q. This is the arithmetic-facing specialisation of the two-row gap: the hypothesis on ell^2 already forces the determinant to be nonzero, and the prime data records the divisibility interface an approximation family would have to supply. -/
theorem primeSupportedTwoSelector_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A₁ B₁ A₂ B₂ : ℤ) (hq : 0 < q)
    (hellq : ¬ (ell : ℤ) ∣ q)
    (hellB₁ : (ell : ℤ) ∣ B₁)
    (hellB₂ : (ell : ℤ) ∣ B₂)
    (hdet : ¬ (ell : ℤ) ^ 2 ∣ A₁ * B₂ - A₂ * B₁) :
    (1 : ℝ) / q ≤
        |(B₁ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₁ : ℝ)| ∨
      (1 : ℝ) / q ≤
        |(B₂ : ℝ) * ((a : ℝ) / (q : ℝ)) - (A₂ : ℝ)| := by
  sorry
/-- Let ell be prime with ell dividing B, ell not dividing A, and ell not dividing q > 0. Then |B (a/q) - A| >= 1/q. The prime data certifies the nonvanishing that the unconditional one-row gap takes as a hypothesis. -/
theorem primeSupportedOneRow_rationalGap
    {ell : ℕ} (hell : ell.Prime)
    (a q A B : ℤ) (hq : 0 < q)
    (hellB : (ell : ℤ) ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry
/-- The same conclusion |B (a/q) - A| >= 1/q under prime-power support: ell prime, r nonzero, ell^r dividing B, ell not dividing A, and ell not dividing q > 0. A single copy of ell already suffices for the conclusion; the stronger hypothesis is retained so that a tail exponent can be passed through unchanged. -/
theorem primePowerSupportedOneRow_rationalGap
    {ell r : ℕ} (hell : ell.Prime) (hr : r ≠ 0)
    (a q A B : ℤ) (hq : 0 < q)
    (hellPowB : (ell : ℤ) ^ r ∣ B)
    (hellA : ¬ (ell : ℤ) ∣ A)
    (hellq : ¬ (ell : ℤ) ∣ q) :
    (1 : ℝ) / q ≤
      |(B : ℝ) * ((a : ℝ) / (q : ℝ)) - (A : ℝ)| := by
  sorry
/-- If the second coordinate of each of k pairs of residues modulo N vanishes, then N < 2^k already forces two distinct Boolean selectors with equal selected sums in both coordinates. With one coordinate identically zero the pigeonhole only has to see the other, so the threshold is N rather than N^2. -/
theorem zeroDenominatorCoordinates_binaryCollision
    {N k : ℕ} [NeZero N]
    (w : Fin k → ZMod N × ZMod N)
    (hzero : ∀ i, (w i).2 = 0)
    (hcard : N < 2 ^ k) :
    ∃ s t : Fin k → Bool, s ≠ t ∧
      (∑ i, if s i then w i else 0) = ∑ i, if t i then w i else 0 := by
  sorry
end PalomarCorpus.E1049.PrimeSupportSelectors

namespace PalomarCorpus.E1049.PublishedHeightRegions
/-- The parameter region log b / log a < 1/2 - 1/pi^2 of the published Bundschuh-Vaananen criterion, written for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This records only the elementary parameter inequality; their analytic irrationality theorem is not internalised, so membership is applicability of a method rather than an irrationality statement. -/
noncomputable def BundschuhVaananenHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < 1 / 2 - 1 / Real.pi ^ 2
/-- The parameter region log b / log a < 81/200 for a reduced rational base a/b, the definition itself imposing no coprimality, positivity or ordering on a and b. This threshold is defined here as an elementary sub-boundary of the region reached by the project's separate ordinary rational-base theorem; it is not a published criterion and carries no analytic hypothesis. -/
noncomputable def ZudilinHeightRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < (81 : ℝ) / 200
/-- The exact integer comparison 3^81 < 2^200, the verified numerical fact that places the base 3/2 beyond the 81/200 threshold. -/
theorem threeHalves_zudilin_power_obstruction :
    3 ^ 81 < 2 ^ 200 := by
  sorry
/-- The real inequality 81/200 < log 2 / log 3, obtained by taking logarithms in the integer comparison above. -/
theorem eightyOneTwoHundredths_lt_threeHalves_log_ratio :
    (81 : ℝ) / 200 < Real.log 2 / Real.log 3 := by
  sorry
/-- The base 3/2 does not satisfy log 2 / log 3 < 81/200, so it lies outside the region defined above. This is a boundary of method applicability; it proves neither rationality nor irrationality of the corresponding Lambert value. -/
theorem threeHalves_outside_zudilinHeightRegion :
    ¬ ZudilinHeightRegion 3 2 := by
  sorry
/-- The base 3/2 also lies outside the Bundschuh-Vaananen region, since 1/2 - 1/pi^2 = 0.398678816... is below 81/200 and log 2 / log 3 = 0.63092975... already exceeds the larger threshold. Inapplicability of that published criterion proves neither rationality nor irrationality. -/
theorem threeHalves_outside_bundschuhVaananenHeightRegion :
    ¬ BundschuhVaananenHeightRegion 3 2 := by
  sorry
end PalomarCorpus.E1049.PublishedHeightRegions
