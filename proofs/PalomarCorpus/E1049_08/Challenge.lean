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
open Finset
open Topology

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

namespace PalomarCorpus.E1049.PaperStatementsU
open Filter
open Finset
open scoped Topology
open scoped BigOperators
open Topology
/-- Local definition leadC, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def leadC (N : ℕ) : ℝ := ((N.factorial : ℝ) ^ 2 * ((N + 1).factorial : ℝ)) / 2 ^ N
/-- Local definition qPochhammerFinite, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammerFinite (a q : ℝ) (n : ℕ) : ℝ :=
  ∏ k ∈ Finset.range n, (1 - a * q ^ k)
/-- Local definition qPochhammerInfinity, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def qPochhammerInfinity (a q : ℝ) : ℝ :=
  Real.exp (∑' k : ℕ, Real.log (1 - a * q ^ k))
/-- Local definition actualMomentTerm, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualMomentTerm (q : ℝ) (m t : ℕ) : ℝ :=
  q ^ ((m + 1) * t) * (qPochhammerFinite q q m) ^ 3 *
    qPochhammerFinite (q ^ (t + 1)) q m /
      qPochhammerFinite (q ^ (m + t + 1)) q (m + 1)
/-- Local definition actualMoment, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualMoment (q : ℝ) (m : ℕ) : ℝ :=
  ∑' t : ℕ, actualMomentTerm q m t
/-- Local definition actualMomentHankel, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def actualMomentHankel (q : ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => actualMoment q (i.val + j.val)
/-- Local definition lambertTerm, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambertTerm {K : Type*} [NormedField K] (z : K) (n : ℕ) : K :=
  z ^ n / (1 - z ^ n)
/-- Local definition lambert, copied so the compared statements of this entry elaborate against Mathlib alone. -/
noncomputable def lambert {K : Type*} [NormedField K] (z : K) : K :=
  ∑' n : ℕ, lambertTerm z n
/-- States res:sharp-fixed-base from the short record for Erdős problem #1049. Transported from ErdosProblems.Erdos1049.PaperCompleteR21.SharpFixedBase.sharp_fixed_base_exists in the substantive development, whose statement was refereed against the paper in the coverage ledger. -/
theorem sharp_fixed_base_exists {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    ∃ K : ℝ, 0 < K ∧
      Tendsto (fun N : ℕ => (actualMomentHankel q N).det /
        (K * leadC N * q ^ (N * (N - 1) * (2 * N - 1) / 6) *
          qPochhammerInfinity q q ^ (2 * N) *
          (N : ℝ) ^ (-8 * lambert q))) atTop (𝓝 1) := by
  sorry
end PalomarCorpus.E1049.PaperStatementsU
