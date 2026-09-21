/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.PaperFixedStartResidueR14

namespace Erdos249257.ExternalVerification269FixedStartResidue

open Filter
open scoped Topology BigOperators

noncomputable def DyadicInternalPower (p a e : ℕ) : Prop :=
  2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)

noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ :=
  by
    classical
    exact
      2 *
        (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) *
        (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)

noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ :=
  if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))

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

noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ :=
  p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x

noncomputable def dyadicNormalizedTailStateR235
    (tail : ℕ → ℝ) (a : ℕ) : ℝ :=
  ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a

noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ :=
  ∑ e ∈ dyadicSmoothShell235 a,
    ((threePrimeHeight 2 3 5
      (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)

noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ :=
  dyadicShellMassQ235 a

noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ :=
  ∑' n : ℕ, dyadicShellMassR235 (a + n)

noncomputable def trueNormalizedState (a : ℕ) : ℝ :=
  dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a

noncomputable def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ
  | 0 => 0
  | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len)

noncomputable def actualWindowProduct (lo len : ℕ) : ℕ :=
  ∏ j ∈ Finset.range len, dyadicBlockBase235 (lo + j)

noncomputable abbrev actualWindowForcing (lo len : ℕ) : ℤ :=
  windowForcing (fun a => (dyadicBlockBase235 a : ℤ))
    (fun a => (dyadicOrderedBlockDigit235 a : ℤ)) lo len

theorem eventually_fixedStartResidue_formula (B lo : ℕ) (hB : 0 < B) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        ((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) *
            (actualWindowProduct lo h : ℝ) -
          (B : ℝ) * trueNormalizedState lo *
            (actualWindowProduct lo h : ℝ) +
          (B : ℝ) * trueNormalizedState (lo + h) := by
  have hforcing (b e : ℕ → ℤ) (s n : ℕ) :
      windowForcing b e s n = ErdosProblems.Erdos269.windowForcing b e s n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [windowForcing, ErdosProblems.Erdos269.windowForcing, ih]
  simpa only [hforcing, DyadicInternalPower,
    dyadicBlockBase235,
    leastPositiveResidue,
    smooth3Val,
    strictSmoothExponents,
    strictSmoothShell,
    dyadicSmoothShell235,
    dyadicBeforeThresholdCount235,
    dyadicOrderedBlockDigit235,
    threePrimeHeight,
    dyadicNormalizedTailStateR235,
    dyadicShellMassQ235,
    dyadicShellMassR235,
    dyadicShellTsumTailR235,
    trueNormalizedState,
    windowForcing,
    actualWindowProduct,
    actualWindowForcing,
    ErdosProblems.Erdos269.DyadicInternalPower,
    ErdosProblems.Erdos269.dyadicBlockBase235,
    ErdosProblems.Erdos269.leastPositiveResidue,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.strictSmoothExponents,
    ErdosProblems.Erdos269.strictSmoothShell,
    ErdosProblems.Erdos269.dyadicSmoothShell235,
    ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
    ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
    ErdosProblems.Erdos269.dyadicShellMassQ235,
    ErdosProblems.Erdos269.dyadicShellMassR235,
    ErdosProblems.Erdos269.dyadicShellTsumTailR235,
    ErdosProblems.Erdos269.trueNormalizedState,
    ErdosProblems.Erdos269.windowForcing,
    ErdosProblems.Erdos269.PaperR7.actualWindowProduct,
    ErdosProblems.Erdos269.PaperR7.actualWindowForcing] using
    ErdosProblems.Erdos269.PaperR14.eventually_fixedStartResidue_formula B lo hB

theorem fixedStartResidue_ratio_tendsto (B lo : ℕ) (hB : 0 < B) :
    Tendsto
      (fun h : ℕ =>
        (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) /
            (actualWindowProduct lo h : ℝ))
      atTop
      (nhds (((⌈(B : ℝ) * trueNormalizedState lo⌉ : ℤ) : ℝ) -
        (B : ℝ) * trueNormalizedState lo)) := by
  have hforcing (b e : ℕ → ℤ) (s n : ℕ) :
      windowForcing b e s n = ErdosProblems.Erdos269.windowForcing b e s n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [windowForcing, ErdosProblems.Erdos269.windowForcing, ih]
  simpa only [hforcing, DyadicInternalPower,
    dyadicBlockBase235,
    leastPositiveResidue,
    smooth3Val,
    strictSmoothExponents,
    strictSmoothShell,
    dyadicSmoothShell235,
    dyadicBeforeThresholdCount235,
    dyadicOrderedBlockDigit235,
    threePrimeHeight,
    dyadicNormalizedTailStateR235,
    dyadicShellMassQ235,
    dyadicShellMassR235,
    dyadicShellTsumTailR235,
    trueNormalizedState,
    windowForcing,
    actualWindowProduct,
    actualWindowForcing,
    ErdosProblems.Erdos269.DyadicInternalPower,
    ErdosProblems.Erdos269.dyadicBlockBase235,
    ErdosProblems.Erdos269.leastPositiveResidue,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.strictSmoothExponents,
    ErdosProblems.Erdos269.strictSmoothShell,
    ErdosProblems.Erdos269.dyadicSmoothShell235,
    ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
    ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
    ErdosProblems.Erdos269.dyadicShellMassQ235,
    ErdosProblems.Erdos269.dyadicShellMassR235,
    ErdosProblems.Erdos269.dyadicShellTsumTailR235,
    ErdosProblems.Erdos269.trueNormalizedState,
    ErdosProblems.Erdos269.windowForcing,
    ErdosProblems.Erdos269.PaperR7.actualWindowProduct,
    ErdosProblems.Erdos269.PaperR7.actualWindowForcing] using
    ErdosProblems.Erdos269.PaperR14.fixedStartResidue_ratio_tendsto B lo hB

theorem eventually_fixedStartResidue_eq_tail_of_integral
    (B lo : ℕ) (hB : 0 < B) (hInt : ∃ z : ℤ, (B : ℝ) * trueNormalizedState lo = z) :
    ∀ᶠ h in atTop,
      (leastPositiveResidue (actualWindowProduct lo h)
          (-((B : ℤ) * actualWindowForcing lo h)) : ℝ) =
        (B : ℝ) * trueNormalizedState (lo + h) := by
  have hforcing (b e : ℕ → ℤ) (s n : ℕ) :
      windowForcing b e s n = ErdosProblems.Erdos269.windowForcing b e s n := by
    induction n with
    | zero => rfl
    | succ n ih =>
        simp only [windowForcing, ErdosProblems.Erdos269.windowForcing, ih]
  simpa only [hforcing, DyadicInternalPower,
    dyadicBlockBase235,
    leastPositiveResidue,
    smooth3Val,
    strictSmoothExponents,
    strictSmoothShell,
    dyadicSmoothShell235,
    dyadicBeforeThresholdCount235,
    dyadicOrderedBlockDigit235,
    threePrimeHeight,
    dyadicNormalizedTailStateR235,
    dyadicShellMassQ235,
    dyadicShellMassR235,
    dyadicShellTsumTailR235,
    trueNormalizedState,
    windowForcing,
    actualWindowProduct,
    actualWindowForcing,
    ErdosProblems.Erdos269.DyadicInternalPower,
    ErdosProblems.Erdos269.dyadicBlockBase235,
    ErdosProblems.Erdos269.leastPositiveResidue,
    ErdosProblems.Erdos269.smooth3Val,
    ErdosProblems.Erdos269.strictSmoothExponents,
    ErdosProblems.Erdos269.strictSmoothShell,
    ErdosProblems.Erdos269.dyadicSmoothShell235,
    ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
    ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
    ErdosProblems.Erdos269.threePrimeHeight,
    ErdosProblems.Erdos269.dyadicNormalizedTailStateR235,
    ErdosProblems.Erdos269.dyadicShellMassQ235,
    ErdosProblems.Erdos269.dyadicShellMassR235,
    ErdosProblems.Erdos269.dyadicShellTsumTailR235,
    ErdosProblems.Erdos269.trueNormalizedState,
    ErdosProblems.Erdos269.windowForcing,
    ErdosProblems.Erdos269.PaperR7.actualWindowProduct,
    ErdosProblems.Erdos269.PaperR7.actualWindowForcing] using
    ErdosProblems.Erdos269.PaperR14.eventually_fixedStartResidue_eq_tail_of_integral B lo hB hInt

end Erdos249257.ExternalVerification269FixedStartResidue
