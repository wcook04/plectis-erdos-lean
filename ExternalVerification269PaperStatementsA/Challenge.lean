/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #269

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos269.DyadicBlockMassIdentity`,
`ErdosProblems.Erdos269.DyadicBlockThresholdPartition`,
`ErdosProblems.Erdos269.PaperCompleteR20.FixedBaseRecoding`,
`ErdosProblems.Erdos269.PaperCompleteR20.LiteralTriangle`,
`ErdosProblems.Erdos269.PaperCompleteR20.LiteralTriangleReal`,
`ErdosProblems.Erdos269.PaperCompleteR20.PhaseStripDecomposition`,
`ErdosProblems.Erdos269.PaperCompleteR20.StripDecomposition`,
`ErdosProblems.Erdos269.PaperCompleteR20.WeightedShiftArithmetic`,
`ErdosProblems.Erdos269.PaperCompleteR20.WeightedShiftValue`,
`ErdosProblems.Erdos269.PaperExactDenominatorR13`,
`ErdosProblems.Erdos269.PaperR7ActualOrbit`, `ErdosProblems.Erdos269.PaperR7BasicAssembly`,
`ErdosProblems.Erdos269.PaperR7ModularMinors`,
`ErdosProblems.Erdos269.PaperR7SeriesIdentification`,
`ErdosProblems.Erdos269.RestrictedFloorSum`, `ErdosProblems.Erdos269.ThreePrimeRunningLcm`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification269PaperStatementsA

noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)

noncomputable def cubicShiftCoefficient : ℕ → ℤ
  | 0 => 1
  | 1 => -3
  | 2 => 3
  | _ => -1

noncomputable def entryStrip {α : Type*} [DecidableEq α] (T : ℕ → Finset α) : ℕ → Finset α
  | 0 => T 0
  | n + 1 => T (n + 1) \ T n

noncomputable def triangleLogPoint (v : ℕ × ℕ) : ℝ :=
  (v.1 : ℝ) * Real.logb 2 3 + (v.2 : ℝ) * Real.logb 2 5

noncomputable def triangleTheta (p : ℕ) : ℝ := 1 / Real.logb 2 p

noncomputable def literalLogWeight (a : ℕ) (v : ℕ × ℕ) : ℕ :=
  3 ^ (⌊((a : ℝ) + 1) * triangleTheta 3⌋₊ -
    ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta 3⌋₊) *
  5 ^ (⌊((a : ℝ) + 1) * triangleTheta 5⌋₊ -
    ⌊((a : ℝ) + Int.fract (triangleLogPoint v)) * triangleTheta 5⌋₊)

noncomputable def triangleOddPart (v : ℕ × ℕ) : ℕ := 3 ^ v.1 * 5 ^ v.2

noncomputable def literalTriangle (a : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (a + 1)).product (Finset.range (a + 1))).filter
    (fun v => triangleOddPart v < 2 ^ (a + 1))

noncomputable def phaseFloor (p a : ℕ) (t : ℝ) : ℤ :=
  ⌊((a : ℝ) + t) * triangleTheta p⌋

noncomputable def phaseCarry (p a : ℕ) (t : ℝ) (u : ℕ) : ℤ :=
  phaseFloor p (a + u) t - phaseFloor p a t - phaseFloor p u 0

noncomputable def phaseChi (a : ℕ) (t : ℝ) (u : ℕ) : ℝ :=
  (3 : ℝ) ^ (-phaseCarry 3 a t u) * (5 : ℝ) ^ (-phaseCarry 5 a t u)

noncomputable def phaseOmega (a : ℕ) (t : ℝ) : ℝ :=
  (3 : ℝ) ^ (phaseFloor 3 a 1 - phaseFloor 3 a t) *
    (5 : ℝ) ^ (phaseFloor 5 a 1 - phaseFloor 5 a t)

noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ :=
  p ^ i * q ^ j * r ^ k

noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x

noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothExponents p q r y \ strictSmoothExponents p q r x

noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))

noncomputable def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ :=
  ((dyadicSmoothShell235 a).filter fun e =>
    smooth3Val 2 3 5 e.1 e.2.1 e.2.2 <
      p ^ Nat.log p (2 ^ (a + 1))).card

noncomputable def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ :=
  if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then
    (dyadicSmoothShell235 a).card +
      10 * dyadicBeforeThresholdCount235 3 a +
      4 * dyadicBeforeThresholdCount235 5 a
  else
    (dyadicSmoothShell235 a).card +
      2 * dyadicBeforeThresholdCount235 3 a +
      12 * dyadicBeforeThresholdCount235 5 a

noncomputable def recodedCoefficient (q a : ℕ) : ℝ :=
  (dyadicOrderedBlockDigit235 a : ℝ) * (q : ℝ) ^ (a + 1) /
    (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℝ)

noncomputable abbrev shiftHeight (n : ℕ) : ℕ := threePrimeHeight 2 3 5 (2 ^ n)

noncomputable def shiftGamma (a t : ℕ) : ℝ :=
  (shiftHeight t : ℝ) * (shiftHeight (a + 1) : ℝ) / (shiftHeight (a + t + 1) : ℝ)

noncomputable def shiftedPrefix (t : ℕ) : ℝ :=
  (shiftHeight t : ℝ) * ∑ k ∈ Finset.range t,
    (dyadicOrderedBlockDigit235 k : ℝ) / (shiftHeight (k + 1) : ℝ)

noncomputable def shiftedCorrection (c : ℕ → ℤ) (σ r : ℕ) : ℝ :=
  15 * ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftedPrefix (j * r)

noncomputable def shiftedLeading (c : ℕ → ℤ) (σ r : ℕ) : ℤ :=
  15 * ∑ j ∈ Finset.range (σ + 1), c j * (shiftHeight (j * r) : ℤ)

noncomputable def shiftedNumerator (c : ℕ → ℤ) (σ r a : ℕ) : ℝ :=
  15 * ∑ j ∈ Finset.range (σ + 1), (c j : ℝ) * shiftGamma a (j * r) *
    (dyadicOrderedBlockDigit235 (a + j * r) : ℝ)

noncomputable def shiftedQuadraticConstant (c : ℕ → ℤ) (σ : ℕ) : ℝ :=
  225 * ∑ j ∈ Finset.range (σ + 1), |(c j : ℝ)| * (max 1 j : ℝ) ^ 2

noncomputable def triangleQuadraticDenominator : ℝ :=
  (2 * Real.logb 2 3 + 1) * (2 * Real.logb 2 5 + 1)

noncomputable def triangleRectangleSide (a p : ℕ) : ℕ :=
  ⌊(a : ℝ) / (2 * Real.logb 2 p)⌋₊ + 1

noncomputable def ClearingCondition (u v w a : ℕ) : Prop :=
  1 ≤ a ∧ 2 ^ (u + 1) ≤ 2 ^ a ∧ 3 ^ v ≤ 2 ^ a ∧ 5 ^ w ≤ 2 ^ a

noncomputable abbrev Exponent235 := ℕ × ℕ × ℕ

noncomputable def exponentValue235 (e : Exponent235) : ℕ :=
  smooth3Val 2 3 5 e.1 e.2.1 e.2.2

noncomputable def Smooth235 := {x : ℕ // x ∈ Set.range exponentValue235}

noncomputable def kernelMod235 (B i j k : ℕ) : ZMod B :=
  (threePrimeHeight 2 3 5 (smooth3Val 2 3 5 i j k) : ZMod B)⁻¹

noncomputable def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) :=
  ((Finset.range (Nat.log p x + 1)).product
      ((Finset.range (Nat.log q x + 1)).product
        (Finset.range (Nat.log r x + 1)))).filter
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x

noncomputable def smoothPrefixLcm (p q r x : ℕ) : ℕ :=
  (smoothPrefixExponents p q r x).lcm
    fun e => smooth3Val p q r e.1 e.2.1 e.2.2

noncomputable def smoothReciprocal235 (x : Smooth235) : ℝ :=
  (smoothPrefixLcm 2 3 5 x.val : ℝ)⁻¹

noncomputable def paperSeries235 : ℝ := ∑' x : Smooth235, smoothReciprocal235 x

noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)

noncomputable def positivePrimePowers (p count : ℕ) : Finset ℕ :=
  (Finset.range count).image fun e => p ^ (e + 1)

noncomputable def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ :=
  (positivePrimePowers p count ∪ positivePrimePowers q count) ∪
    positivePrimePowers r count

noncomputable def threePrimeJumpSetWithOrigin (p q r count : ℕ) : Finset ℕ :=
  insert 1 (threePrimePositiveJumpSet p q r count)

noncomputable def threePrimeKernelQ (p q r i j k : ℕ) : ℚ :=
  (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹

/-- States long269:res:strip-decomposition from the long record for Erdős problem #269.
Transported from ErdosProblems.Erdos269.PaperCompleteR20.actual_cubic_no_crossing_strips in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem actual_cubic_no_crossing_strips (a r : ℕ)
    (hcross : ∀ ν : ℕ, ν ≤ 3 → ∀ v ∈ literalTriangle (a + ν * r),
      phaseCarry 3 a (Int.fract (triangleLogPoint v)) (ν * r) = 0 ∧
      phaseCarry 5 a (Int.fract (triangleLogPoint v)) (ν * r) = 0) :
    shiftedNumerator cubicShiftCoefficient 3 r a / 15 =
      -(∑ v ∈ literalTriangle (a + r) \ literalTriangle a,
          phaseOmega a (Int.fract (triangleLogPoint v))) +
        2 * (∑ v ∈ literalTriangle (a + 2 * r) \ literalTriangle (a + r),
          phaseOmega a (Int.fract (triangleLogPoint v))) -
        (∑ v ∈ literalTriangle (a + 3 * r) \ literalTriangle (a + 2 * r),
          phaseOmega a (Int.fract (triangleLogPoint v))) := by
  sorry

/-- States long269:res:strip-decomposition from the long record for Erdős problem #269.
Transported from ErdosProblems.Erdos269.PaperCompleteR20.actual_weighted_strip_decomposition
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem actual_weighted_strip_decomposition (c : ℕ → ℤ) (σ r a : ℕ) :
    shiftedNumerator c σ r a / 15 =
      ∑ s ∈ Finset.range (σ + 1),
        ∑ v ∈ entryStrip (fun n => literalTriangle (a + n * r)) s,
          phaseOmega a (Int.fract (triangleLogPoint v)) *
            ∑ ν ∈ Finset.Icc s σ, (c ν : ℝ) *
              phaseChi a (Int.fract (triangleLogPoint v)) (ν * r) := by
  sorry

/-- States long269:res:fixed-base-recoding from the long record for Erdős problem #269.
Transported from ErdosProblems.Erdos269.PaperCompleteR20.fixed_base_recoding_whole in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem fixed_base_recoding_whole :
    (HasSum (fun a : ℕ => recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 30 a / (30 : ℝ) ^ (a + 1)|)) ∧
    (HasSum (fun a : ℕ => recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)) (paperSeries235 / 2)) ∧
    (Summable (fun a : ℕ => |recodedCoefficient 8 a / (8 : ℝ) ^ (a + 1)|)) ∧
    (∀ a : ℕ, (∃ z : ℕ, 0 < z ∧ recodedCoefficient 30 a = (z : ℝ)) ∧
      (15 / 4 : ℝ) ^ (a + 1) ≤ recodedCoefficient 30 a) ∧
    (∀ a : ℕ, (∃ z : ℕ, recodedCoefficient 8 a = (z : ℝ) / (15 : ℝ) ^ (a + 1)) ∧
      0 < recodedCoefficient 8 a ∧ recodedCoefficient 8 a < 225 * ((a + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ q : ℕ, 2 ≤ q →
      ((∀ n : ℕ, 1 ≤ n → threePrimeHeight 2 3 5 (2 ^ n) ∣ q ^ n) ↔ 30 ∣ q) ∧
      ∀ a : ℕ, ((q : ℝ) / 8) ^ (a + 1) ≤ recodedCoefficient q a) := by
  sorry

/-- States long269:res:literal-triangle from the long record for Erdős problem #269. Transported
from ErdosProblems.Erdos269.PaperCompleteR20.literal_triangle_whole in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem literal_triangle_whole :
    (∀ a, dyadicOrderedBlockDigit235 a = ∑ v ∈ literalTriangle a, literalLogWeight a v) ∧
    (∀ a v, v ∈ literalTriangle a →
      literalLogWeight a v = 1 ∨ literalLogWeight a v = 3 ∨
      literalLogWeight a v = 5 ∨ literalLogWeight a v = 15) ∧
    (∀ a, triangleRectangleSide a 3 * triangleRectangleSide a 5 ≤ dyadicOrderedBlockDigit235 a) ∧
    (∀ a : ℕ, (a + 1 : ℝ) ^ 2 / triangleQuadraticDenominator ≤ dyadicOrderedBlockDigit235 a ∧
      (dyadicOrderedBlockDigit235 a : ℝ) ≤ 15 * (a + 1 : ℝ) ^ 2) ∧
    (∀ M : ℝ, ∃ a : ℕ, M < dyadicOrderedBlockDigit235 a) := by
  sorry

/-- States long269:eq:weighted-shift-identity, long269:res:weighted-shift-identity from the long
record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperCompleteR20.weighted_shift_whole in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem weighted_shift_whole (c : ℕ → ℤ) (σ r : ℕ) :
    (∀ a t, shiftGamma a t = 1 ∨ shiftGamma a t = 1 / 3 ∨
      shiftGamma a t = 1 / 5 ∨ shiftGamma a t = 1 / 15) ∧
    (∀ a, ∃ z : ℤ, shiftedNumerator c σ r a = (z : ℝ)) ∧
    (∃ z : ℤ, shiftedCorrection c σ r = (z : ℝ)) ∧
    HasSum (fun a : ℕ => shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ))
      ((shiftedLeading c σ r : ℝ) * (paperSeries235 / 2) - shiftedCorrection c σ r) ∧
    Summable (fun a : ℕ => |shiftedNumerator c σ r a / (shiftHeight (a + 1) : ℝ)|) ∧
    (∀ a, |shiftedNumerator c σ r a| ≤
      shiftedQuadraticConstant c σ * ((a + r + 1 : ℕ) : ℝ) ^ 2) ∧
    (∀ J : ℕ, J ≤ σ → (∀ j, J < j → j ≤ σ → c j = 0) →
      (∑ j ∈ Finset.range J, |(c j : ℝ)| / (2 : ℝ) ^ ((J - j) * r)) < |(c J : ℝ)| →
      shiftedLeading c σ r ≠ 0) := by
  sorry

/-- States long269:res:exact-denominator, res:exact-onset from the long record and the short
record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperR13.clearingCondition_iff_max in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem clearingCondition_iff_max {u v w a : ℕ} :
    ClearingCondition u v w a ↔
      1 ≤ a ∧ max (2 ^ (u + 1)) (max (3 ^ v) (5 ^ w)) ≤ 2 ^ a := by
  sorry

/-- States res:admissible-modular-minors from the short record for Erdős problem #269.
Transported from ErdosProblems.Erdos269.PaperR7.admissible_modular_minors in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem admissible_modular_minors (n : ℕ) :
    ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧
      (∀ k : ℕ,
        (Matrix.det fun i j : Fin n => threePrimeKernelQ 2 3 5 (I i) (J j) k) ≠ 0) ∧
      (∀ B : ℕ, 2 ≤ B → Nat.Coprime B 30 → ∀ k : ℕ,
        IsUnit (Matrix.det fun i j : Fin n => kernelMod235 B (I i) (J j) k) ∧
        IsUnit (Matrix.of fun i j : Fin n => kernelMod235 B (I i) (J j) k)) := by
  sorry

/-- States long269:res:count, res:cell from the long record and the short record for Erdős
problem #269. Transported from ErdosProblems.Erdos269.PaperR7.paper_jump_count in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem paper_jump_count {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (n : ℕ) :
    (threePrimePositiveJumpSet p q r n).card = 3 * n ∧
    (threePrimeJumpSetWithOrigin p q r n).card = 3 * n + 1 := by
  sorry

/-- States long269:res:rank from the long record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperR7.paper_two_by_two_fixture in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_two_by_two_fixture :
    threePrimeKernelQ 2 3 5 0 0 0 = 1 ∧
    threePrimeKernelQ 2 3 5 0 1 0 = 1 / 6 ∧
    threePrimeKernelQ 2 3 5 1 0 0 = 1 / 2 ∧
    threePrimeKernelQ 2 3 5 1 1 0 = 1 / 60 ∧
    (Matrix.det (fun i j : Fin 2 => threePrimeKernelQ 2 3 5 i j 0)) = -(1 / 15 : ℚ) ∧
    (Matrix.det (fun i j : Fin 2 => threePrimeKernelQ 2 3 5 i j 0)) ≠ 0 := by
  sorry

/-- States long269:res:infinite-rank, long269:res:lead-infinite-rank, res:infinite-rank from the
long record and the short record for Erdős problem #269. Transported from
ErdosProblems.Erdos269.PaperR7.paper_uniform_rank_and_nonseparation in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem paper_uniform_rank_and_nonseparation {p q r : ℕ}
    (hp : p.Prime) (hq : q.Prime) (hr : r.Prime)
    (_hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    (∀ n : ℕ, ∃ I J : Fin n → ℕ,
      Function.Injective I ∧ Function.Injective J ∧
      ∀ k : ℕ, (Matrix.det fun a b : Fin n =>
        threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧
    (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ),
      ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k) := by
  sorry

/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for
Erdős problem #269. Transported from ErdosProblems.Erdos269.PaperR7.radix_eq_height_ratio in
the substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem radix_eq_height_ratio (a : ℕ) :
    (dyadicBlockBase235 a : ℚ) =
      (threePrimeHeight 2 3 5 (2 ^ (a + 1)) : ℚ) /
        (threePrimeHeight 2 3 5 (2 ^ a) : ℚ) := by
  sorry

/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for
Erdős problem #269. Transported from ErdosProblems.Erdos269.dyadicBlockBase235_cases in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem dyadicBlockBase235_cases (a : ℕ) :
    dyadicBlockBase235 a = 2 ∨
      dyadicBlockBase235 a = 6 ∨
      dyadicBlockBase235 a = 10 ∨
      dyadicBlockBase235 a = 30 := by
  sorry

/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for
Erdős problem #269. Transported from ErdosProblems.Erdos269.dyadicBlockBase235_mem_interval
in the substantive development, whose statement was refereed against the paper in the
coverage ledger. -/
theorem dyadicBlockBase235_mem_interval (a : ℕ) :
    2 ≤ dyadicBlockBase235 a ∧ dyadicBlockBase235 a ≤ 30 := by
  sorry

/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for
Erdős problem #269. Transported from
ErdosProblems.Erdos269.dyadicInternalPower_exponent_unique in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem dyadicInternalPower_exponent_unique
    {p a e f : ℕ} (hp : 2 ≤ p)
    (he : DyadicInternalPower p a e)
    (hf : DyadicInternalPower p a f) :
    e = f := by
  sorry

/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for
Erdős problem #269. Transported from
ErdosProblems.Erdos269.exists_dyadicInternalPower_iff_log_succ in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem exists_dyadicInternalPower_iff_log_succ
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p) :
    (∃ e, DyadicInternalPower p a e) ↔
      Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a) + 1 := by
  sorry

/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for
Erdős problem #269. Transported from
ErdosProblems.Erdos269.log_dyadic_succ_eq_of_no_internalPower in the substantive
development, whose statement was refereed against the paper in the coverage ledger. -/
theorem log_dyadic_succ_eq_of_no_internalPower
    {p a : ℕ} (hp : 2 < p) (hpOdd : Odd p)
    (hNo : ¬ ∃ e, DyadicInternalPower p a e) :
    Nat.log p (2 ^ (a + 1)) = Nat.log p (2 ^ a) := by
  sorry

/-- States long269:eq:dyadic-alphabet, long269:res:dyadic-alphabet from the long record for
Erdős problem #269. Transported from
ErdosProblems.Erdos269.threePrimeHeight_dyadicBlock_succ in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem threePrimeHeight_dyadicBlock_succ (a : ℕ) :
    threePrimeHeight 2 3 5 (2 ^ (a + 1)) =
      dyadicBlockBase235 a * threePrimeHeight 2 3 5 (2 ^ a) := by
  sorry

end Erdos249257.ExternalVerification269PaperStatementsA
