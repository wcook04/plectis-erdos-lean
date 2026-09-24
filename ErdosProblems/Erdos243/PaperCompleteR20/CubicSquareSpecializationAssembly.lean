import ErdosProblems.Erdos243.PaperCompleteR11.CubicFieldScale
import ErdosProblems.Erdos243.PaperCompleteR11.PrimitiveMultiplierSupply
import ErdosProblems.Erdos243.PaperCompleteR11.CubicQuarticCertificates

/-!
# Erdős 243: the exact post-specialisation cubic contradiction

This module isolates the part of the fixed-cubic exclusion after the number-
field specialisation.  Starting from the actual primitive positive orbit and
zero lower density of failures, the existing arithmetic develops the unit
constant and irreducibility.  If the Chebotarev specialisation has produced
the required square in the cubic root field, the algebraic classification
forces scale twelve, and the explicit modulo-seven certificate contradicts
zero lower density.

The square-specialisation hypothesis is the precise remaining number-field
input.  It is not a reformulation of the density conclusion.
-/

noncomputable section

namespace ErdosProblems.Erdos243.PaperCompleteR20

open ErdosProblems.Erdos243.PaperCompleteR11
open Polynomial

/-- The complete arithmetic assembly after the missing Chebotarev
square-specialisation step.  In particular, neither the unit constant,
irreducibility, scale twelve, nor the terminal modulo-seven obstruction is
assumed. -/
theorem primitive_cubic_zero_density_impossible_of_square_specialisation
    {L : Type*} [Field L] [Algebra ℚ L]
    (a u v : ℕ → ℕ) (m : ℕ) (c : ℤ) (T : ℕ) (hm : 0 < m)
    (hv : ∀ n, T ≤ n → 0 < v n)
    (hnum : ∀ n, T ≤ n → u (n + 1) + v n = a n * u n)
    (hden : ∀ n, T ≤ n → v (n + 1) = a n * v n)
    (hcop : ∀ n, T ≤ n → Nat.Coprime (u n) (v n))
    (hzero : ZeroLowerDensity
      {n : ℕ | (u n : ℤ) ≠ (m : ℤ) * risingBinomial n + c})
    (α β : L)
    (hroot : α ^ 3 = α - algebraMap ℚ L (6 * (c : ℚ) / (m : ℚ)))
    (hβmem : β ∈ IntermediateField.adjoin ℚ ({α} : Set L))
    (hβ : β ^ 2 = α ^ 2 - 1) : False := by
  obtain ⟨hc, _hcd, _hpair, _hlate, _hprimes, hirr⟩ :=
    primitive_zero_density_multiplier_irreducibility
      a u v m c T hm hv hnum hden hcop hzero
  have hcQ : (c : ℚ) = 1 ∨ (c : ℚ) = -1 := by
    rcases hc with rfl | rfl <;> norm_num
  have hm12 : m = 12 :=
    cubic_scale_twelve_of_square_in_adjoin m (c : ℚ) hm hcQ
      α β hirr hroot hβmem hβ
  have hnumZ : ∀ n, T ≤ n →
      (u (n + 1) : ℤ) + (v n : ℤ) = (a n : ℤ) * (u n : ℤ) := by
    intro n hn
    exact_mod_cast hnum n hn
  have hdenZ : ∀ n, T ≤ n →
      (v (n + 1) : ℤ) = (a n : ℤ) * (v n : ℤ) := by
    intro n hn
    exact_mod_cast hden n hn
  subst m
  letI : Fact (Nat.Prime 7) := ⟨by decide⟩
  have hratio : (c : ZMod 7) / (12 : ZMod 7) = 1 ∨
      (c : ZMod 7) / (12 : ZMod 7) = 3 ∨
      (c : ZMod 7) / (12 : ZMod 7) = 4 ∨
      (c : ZMod 7) / (12 : ZMod 7) = 6 := by
    have h12 : (12 : ZMod 7) = 5 :=
      (ZMod.natCast_eq_natCast_iff' 12 5 7).2 (by decide)
    have h5 : (5 : ZMod 7) ≠ 0 := by decide
    rcases hc with rfl | rfl
    · have hpos : (1 : ZMod 7) / 12 = 3 := by
        rw [h12]
        apply (div_eq_iff h5).2
        change (1 : ZMod 7) = 15
        exact (ZMod.natCast_eq_natCast_iff' 1 15 7).2 (by decide)
      exact Or.inr (Or.inl hpos)
    · have hneg : ((-1 : ℤ) : ZMod 7) = 6 :=
        (ZMod.intCast_eq_intCast_iff' (-1) 6 7).2 (by decide)
      have hnegRatio : ((-1 : ℤ) : ZMod 7) / 12 = 4 := by
        rw [hneg, h12]
        apply (div_eq_iff h5).2
        change (6 : ZMod 7) = 20
        exact (ZMod.natCast_eq_natCast_iff' 6 20 7).2 (by decide)
      exact Or.inr (Or.inr (Or.inl hnegRatio))
  have hdensity := integral_cubic_mod_seven_quartic_density
    (fun n ↦ (a n : ℤ)) (fun n ↦ (u n : ℤ)) (fun n ↦ (v n : ℤ))
    12 c T hnumZ hdenZ (by decide) hratio
  exact (hzero.not_positive_lower_bound (1 / 7) (by norm_num)) hdensity

#print axioms ErdosProblems.Erdos243.PaperCompleteR20.primitive_cubic_zero_density_impossible_of_square_specialisation

end ErdosProblems.Erdos243.PaperCompleteR20
