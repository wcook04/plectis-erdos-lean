import ErdosProblems.Erdos1049.PaperR17.SourceConsumers

namespace ErdosProblems.Erdos1049.PaperR17

/-- Exact all-power quantitative endpoint; composition of the proved region
and uniform-over-powers measure theorem. -/
theorem rational_base_contour_measure
    (a b : ℕ) (hb : 0 < b) (hab : b < a)
    (hregion : ErdosProblems.Erdos1049.ZudilinContourRegion a b) :
    ∀ r : ℕ, 0 < r →
      Irrational (ErdosProblems.Erdos1049.PaperR7.paperLambert (((a : ℝ) / b) ^ r)) ∧
      ErdosProblems.Erdos1049.PaperR11.irrationalityExponent
        (ErdosProblems.Erdos1049.PaperR7.paperLambert (((a : ℝ) / b) ^ r)) ≤
        ErdosProblems.Erdos1049.PaperR10.rationalBaseMeasureBound a b := by
  intro r hr
  constructor
  · have h := rational_base_region (a ^ r) (b ^ r) (Nat.pow_pos hb)
      (Nat.pow_lt_pow_left hab hr.ne')
      (ErdosProblems.Erdos1049.zudilinContourRegion_pow a b r hr hregion)
    simpa only [Nat.cast_pow, div_pow] using h
  · exact rational_base_power_measure a b r hb hab hr hregion

#print axioms rational_base_contour_measure

end ErdosProblems.Erdos1049.PaperR17
