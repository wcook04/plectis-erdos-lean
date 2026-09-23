import Erdos257PeriodNoncollapse.HalfCylinderLargestSkipGap
import Erdos257PeriodNoncollapse.HalfCylinderBoundaryPulse

/-
The paper repository's copy of this module does not declare the results below; they were proved in
this corpus. A shim can only publish a name the library has, so this module keeps them, and keeps them
exactly as they were written: it is the corpus module with every declaration the library already carries
removed, and the shim imported in their place. No statement, hypothesis, proof or name is changed here.
-/

/-!
# Boundary pulse normalization for the largest-skip crossing

When a largest skipped rank `d` lies beyond two thirds of row `s`, every
strictly larger rank `e < s` is too large to divide either new incidence
index `2*s+1` or `2*s+2`.  Hence the completely filled suffix above `d`
contributes no row pulse.

At the first row where the strict inequality would fail, elementary integer
arithmetic leaves exactly two boundary cases: `3*d = 2*s+1` and
`3*d = 2*s+2`.  The pulse at `d` is respectively two or one.  These facts
are the incidence normalization needed by the remaining producer estimate.
-/

namespace Erdos257PeriodNoncollapse

open HalfCylinderIntegerGreedy
open scoped BigOperators

/-- If the largest skipped rank remains strictly late at the next row, then
the boundary rank itself is pulse-invisible.  The stronger inequality
`2 * (s + 1) < 3 * d` places both new incidence indices strictly below the
next possible positive multiple `3 * d`; divisibility by `d` would force
one of them to reach that multiple. -/
theorem rowPulse_eq_zero_of_nextLate_boundary
    {s d : ℕ} (hd2 : 2 ≤ d) (hds : d < s)
    (hnextLate : 2 * (s + 1) < 3 * d) :
    rowPulse s d = 0 := by
  have hone : ¬ d ∣ 2 * s + 1 := by
    intro hdiv
    have htwice : d ∣ 2 * d := ⟨2, by omega⟩
    have hrem : d ∣ (2 * s + 1) - 2 * d := Nat.dvd_sub hdiv htwice
    have hpos : 0 < (2 * s + 1) - 2 * d := by omega
    have hle : d ≤ (2 * s + 1) - 2 * d := Nat.le_of_dvd hpos hrem
    omega
  have htwo : ¬ d ∣ 2 * s + 2 := by
    intro hdiv
    have htwice : d ∣ 2 * d := ⟨2, by omega⟩
    have hrem : d ∣ (2 * s + 2) - 2 * d := Nat.dvd_sub hdiv htwice
    have hpos : 0 < (2 * s + 2) - 2 * d := by omega
    have hle : d ≤ (2 * s + 2) - 2 * d := Nat.le_of_dvd hpos hrem
    omega
  simp [rowPulse, hone, htwo]

end Erdos257PeriodNoncollapse
