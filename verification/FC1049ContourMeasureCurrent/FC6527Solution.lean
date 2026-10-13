import Solutions.ExternalVerification1049ContourMeasurePowers

namespace Erdos1049

namespace RationalBaseContour

open scoped BigOperators

noncomputable def paperLambert (x : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / (x ^ (n + 1) - 1)

noncomputable def trigammaSeries (x : ℝ) : ℝ :=
  ∑' k : ℕ, 1 / ((k : ℝ) + x) ^ 2

noncomputable def zudilinJTerm (u v : ℝ) : ℝ :=
  trigammaSeries u - trigammaSeries v

noncomputable def zudilinJ : ℝ :=
  zudilinJTerm (1 / 14) (1 / 12) + zudilinJTerm (1 / 7) (1 / 6) +
    zudilinJTerm (3 / 14) (1 / 4) + zudilinJTerm (2 / 7) (1 / 3) +
    zudilinJTerm (5 / 14) (2 / 5) + zudilinJTerm (3 / 7) (7 / 15) +
    zudilinJTerm (1 / 2) (8 / 15) + zudilinJTerm (4 / 7) (3 / 5) +
    zudilinJTerm (9 / 14) (2 / 3) + zudilinJTerm (5 / 7) (11 / 15) +
    zudilinJTerm (11 / 14) (4 / 5) + zudilinJTerm (6 / 7) (13 / 15) +
    zudilinJTerm (13 / 14) (14 / 15)

noncomputable def zudilinC1 : ℝ := 1091 / 2
noncomputable def zudilinC0 : ℝ := 266 - 3 / Real.pi ^ 2 * (225 - zudilinJ)
noncomputable def zudilinContour : ℝ := zudilinC0 / zudilinC1

def ZudilinContourRegion (a b : ℕ) : Prop :=
  Real.log b / Real.log a < zudilinContour

def reducedApproximationPairs (ξ ν : ℝ) : Set (ℤ × ℕ) :=
  {r | 0 < r.2 ∧ Nat.Coprime r.1.natAbs r.2 ∧
    |ξ - (r.1 : ℝ) / (r.2 : ℝ)| < (r.2 : ℝ) ^ (-ν)}

def approximationExponents (ξ : ℝ) : Set ℝ :=
  {ν | (reducedApproximationPairs ξ ν).Infinite}

/-- Supremum of exponents admitting infinitely many reduced rational approximations.
This real-valued definition is used here only at the finite-exponent irrational values
in the theorem below. -/
noncomputable def irrationalityExponent (ξ : ℝ) : ℝ :=
  sSup (approximationExponents ξ)

noncomputable def rationalBaseMeasureBound (a b : ℕ) : ℝ :=
  (1 - Real.log b / Real.log a) /
    (zudilinContour - Real.log b / Real.log a)

end RationalBaseContour

open RationalBaseContour

theorem erdos_1049.variants.rational_base_contour_measure
    (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hregion : ZudilinContourRegion a b) :
    ∀ r : ℕ, 0 < r →
      Irrational (paperLambert (((a : ℝ) / b) ^ r)) ∧
      irrationalityExponent (paperLambert (((a : ℝ) / b) ^ r)) ≤
        rationalBaseMeasureBound a b := by
  change ExternalVerification1049ContourMeasurePowers.ZudilinContourRegion a b at hregion
  change ∀ r : ℕ, 0 < r →
    Irrational (ExternalVerification1049ContourMeasurePowers.paperLambert (((a : ℝ) / b) ^ r)) ∧
    ExternalVerification1049ContourMeasurePowers.irrationalityExponent
      (ExternalVerification1049ContourMeasurePowers.paperLambert (((a : ℝ) / b) ^ r)) ≤
      ExternalVerification1049ContourMeasurePowers.rationalBaseMeasureBound a b
  exact ExternalVerification1049ContourMeasurePowers.rational_base_contour_measure a b hb hab hregion

#print axioms erdos_1049.variants.rational_base_contour_measure

end Erdos1049
