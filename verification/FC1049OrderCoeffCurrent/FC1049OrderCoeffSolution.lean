/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import ErdosProblems.Erdos1049.AllRow.Producer

open scoped BigOperators

namespace ZudilinHankelInitialTerm

/-- The finite formal q-Pochhammer product. -/
noncomputable def pochhammer (start len : ℕ) : PowerSeries ℤ :=
  ∏ r ∈ Finset.range len,
    (1 - PowerSeries.X ^ (start + r) : PowerSeries ℤ)

/-- The unit factor of the tth normalized moment summand at x = z = 1. -/
noncomputable def normalizedTailUnit (n t : ℕ) : PowerSeries ℤ :=
  pochhammer 1 n ^ 3 * pochhammer (t + 1) n *
    PowerSeries.invOfUnit (pochhammer (n + 1 + t) (n + 1)) 1

/-- The tth normalized moment summand. -/
noncomputable def normalizedTail (n t : ℕ) : PowerSeries ℤ :=
  PowerSeries.X ^ ((n + 1) * t) * normalizedTailUnit n t

/-- Zudilin's normalized moment at x = z = 1. Each coefficient is a finite sum. -/
noncomputable def normalizedMoment (n : ℕ) : PowerSeries ℤ :=
  PowerSeries.mk fun d =>
    ∑ t ∈ Finset.range (d / (n + 1) + 1),
      PowerSeries.coeff d (normalizedTail n t)

/-- The normalized Hankel determinant; the determinant at rank zero is one. -/
noncomputable def hankelDet (N : ℕ) : PowerSeries ℤ :=
  Matrix.det (fun i j : Fin N => normalizedMoment ((i : ℕ) + (j : ℕ)))

theorem first_nonzero_term (N : ℕ) :
    PowerSeries.order (hankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) ∧
    (2 : ℤ) ^ N * PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (hankelDet N) = (N.factorial : ℤ) ^ 2 * ((N + 1).factorial : ℤ) := by
  change PowerSeries.order (ErdosProblems.Erdos1049.zudilinNormalizedHankelDet N) =
      ((N * (N - 1) * (2 * N - 1) / 6 : ℕ) : ℕ∞) ∧
    (2 : ℤ) ^ N * PowerSeries.coeff (N * (N - 1) * (2 * N - 1) / 6)
      (ErdosProblems.Erdos1049.zudilinNormalizedHankelDet N) =
        (N.factorial : ℤ) ^ 2 * ((N + 1).factorial : ℤ)
  exact ⟨ErdosProblems.Erdos1049.order_zudilinNormalizedHankelDet_all N,
    ErdosProblems.Erdos1049.leadingCoeff_zudilinNormalizedHankelDet_all N⟩

end ZudilinHankelInitialTerm

#print axioms ZudilinHankelInitialTerm.first_nonzero_term
