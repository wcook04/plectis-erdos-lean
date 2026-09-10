/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
/-! Palomar challenge for Erdős problem #269. Parent problem remains open. See `PalomarCorpus/README.md`. -/
namespace PalomarCorpus.E269.Shared
noncomputable def DyadicInternalPower (p a e : ℕ) : Prop := 2 ^ a < p ^ e ∧ p ^ e < 2 ^ (a + 1)
noncomputable def dyadicBlockBase235 (a : ℕ) : ℕ := by classical exact 2 * (if ∃ e, DyadicInternalPower 3 a e then 3 else 1) * (if ∃ e, DyadicInternalPower 5 a e then 5 else 1)
noncomputable def leastPositiveResidue (C : ℕ) (x : ℤ) : ℕ := if x % (C : ℤ) = 0 then C else Int.natAbs (x % (C : ℤ))
noncomputable def smooth3Val (p q r i j k : ℕ) : ℕ := p ^ i * q ^ j * r ^ k
noncomputable def strictSmoothExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) := ((Finset.range x).product ((Finset.range x).product (Finset.range x))).filter fun e => smooth3Val p q r e.1 e.2.1 e.2.2 < x
noncomputable def strictSmoothShell (p q r x y : ℕ) : Finset (ℕ × ℕ × ℕ) := strictSmoothExponents p q r y \ strictSmoothExponents p q r x
noncomputable def dyadicSmoothShell235 (a : ℕ) : Finset (ℕ × ℕ × ℕ) := strictSmoothShell 2 3 5 (2 ^ a) (2 ^ (a + 1))
noncomputable def dyadicBeforeThresholdCount235 (p a : ℕ) : ℕ := ((dyadicSmoothShell235 a).filter fun e => smooth3Val 2 3 5 e.1 e.2.1 e.2.2 < p ^ Nat.log p (2 ^ (a + 1))).card
noncomputable def dyadicOrderedBlockDigit235 (a : ℕ) : ℕ := if 3 ^ Nat.log 3 (2 ^ (a + 1)) ≤ 5 ^ Nat.log 5 (2 ^ (a + 1)) then (dyadicSmoothShell235 a).card + 10 * dyadicBeforeThresholdCount235 3 a + 4 * dyadicBeforeThresholdCount235 5 a else (dyadicSmoothShell235 a).card + 2 * dyadicBeforeThresholdCount235 3 a + 12 * dyadicBeforeThresholdCount235 5 a
noncomputable def threePrimeHeight (p q r x : ℕ) : ℕ := p ^ Nat.log p x * q ^ Nat.log q x * r ^ Nat.log r x
noncomputable def dyadicNormalizedTailStateR235 (tail : ℕ → ℝ) (a : ℕ) : ℝ := ((threePrimeHeight 2 3 5 (2 ^ a) : ℝ) / 2) * tail a
noncomputable def dyadicShellMassQ235 (a : ℕ) : ℚ := ∑ e ∈ dyadicSmoothShell235 a, ((threePrimeHeight 2 3 5 (smooth3Val 2 3 5 e.1 e.2.1 e.2.2) : ℚ)⁻¹)
noncomputable def dyadicShellMassR235 (a : ℕ) : ℝ := dyadicShellMassQ235 a
noncomputable def dyadicShellTsumTailR235 (a : ℕ) : ℝ := ∑' n : ℕ, dyadicShellMassR235 (a + n)
noncomputable def trueNormalizedState (a : ℕ) : ℝ := dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a /-- Every true state is pinned exactly above its ordered digit anchor. -/
noncomputable def windowBase (b : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ | 0 => 1 | len + 1 => b (lo + len) * windowBase b lo len
noncomputable def windowForcing (b e : ℕ → ℤ) (lo : ℕ) : ℕ → ℤ | 0 => 0 | len + 1 => b (lo + len) * windowForcing b e lo len + e (lo + len) /-- The exact denominator-dependent producer consumed by the local-window contradiction.  It is deliberately named as a proposition, not asserted. -/
noncomputable def CofinalLocalWindowEscape (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ) : Prop := ∀ B : ℕ, 0 < B → Nat.Coprime B 30 → ∀ lo₀ : ℕ, ∃ lo len : ℕ, lo₀ ≤ lo ∧ 0 < len ∧ 0 < Int.natAbs (windowBase (fun n => b n) lo len) ∧ shortBound B (lo + len) < leastPositiveResidue (Int.natAbs (windowBase (fun n => b n) lo len)) (-((B : ℤ) * windowForcing (fun n => b n) (fun n => m n) lo len)) /-- Cofinal local-window escape rules out a positive reduced carry obeying the matching recurrence and short bound. -/
end PalomarCorpus.E269.Shared
namespace PalomarCorpus.E269.ActualShellOrbit
open scoped BigOperators
export PalomarCorpus.E269.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)
def FarFromIntegers (x δ : ℝ) : Prop := ∀ z : ℤ, δ ≤ |x - (z : ℝ)| /-- The actual infinite shell tail is summable, follows the exact ordered affine orbit, and satisfies the integral-or-cofinally-far alternative. -/
theorem actual_dyadicShellOrbit_recurrence_and_escape : Summable dyadicShellMassR235 ∧ (∀ a : ℕ, dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (a + 1) = dyadicBlockBase235 a * dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a - dyadicOrderedBlockDigit235 a) ∧ ((∃ a : ℕ, ∃ z : ℤ, dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a = (z : ℝ)) ∨ ∀ a₀, ∃ a, a₀ ≤ a ∧ FarFromIntegers (dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a) ((1 : ℝ) / 31)) := by sorry
end PalomarCorpus.E269.ActualShellOrbit
namespace PalomarCorpus.E269.AllScaleLattice
open scoped BigOperators
export PalomarCorpus.E269.Shared (dyadicNormalizedTailStateR235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight)
def heightNormalizer235 (a : ℕ) : ℕ := threePrimeHeight 2 3 5 (2 ^ a) / 2
def dyadicSmoothWindowMassQ235 (start count : ℕ) : ℚ := ∑ i ∈ Finset.range count, dyadicShellMassQ235 (start + i) /-- Every `{2,3,5}`-smooth height strictly below a prime-power boundary has one further copy of that boundary prime available.  This simultaneously exposes the `2`-, `3`-, and `5`-power clearing families. -/
theorem smoothHeight_mul_prime_dvd_boundaryHeight {p m x : ℕ} (hp : p = 2 ∨ p = 3 ∨ p = 5) (hx : 0 < x) (hlt : x < p ^ m) : p * threePrimeHeight 2 3 5 x ∣ threePrimeHeight 2 3 5 (p ^ m) := by sorry
theorem two_mul_heightNormalizer235 (a : ℕ) (ha : 1 ≤ a) : 2 * heightNormalizer235 a = threePrimeHeight 2 3 5 (2 ^ a) := by sorry
theorem heightNormalizer235_mul_windowMass_eq_int (start count : ℕ) : ∃ z : ℕ, (heightNormalizer235 (start + count) : ℚ) * dyadicSmoothWindowMassQ235 start count = (z : ℚ) := by sorry
theorem dyadicShellTsumTailR235_eq_range_add (a k : ℕ) : dyadicShellTsumTailR235 a = ∑ i ∈ Finset.range k, dyadicShellMassR235 (a + i) + dyadicShellTsumTailR235 (a + k) := by sorry
theorem qsmul_normalizedTailState_eq_int_of_value_eq_rat {p q : ℤ} (hq : 0 < q) (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) {a : ℕ} (ha : 1 ≤ a) : ∃ k : ℤ, (q : ℝ) * dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 a = (k : ℝ) := by sorry
theorem exists_normalizedTailState_collision_of_value_eq_rat {p q : ℤ} (hq : 0 < q) (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) : ∃ i j : ℕ, i < j ∧ ∃ z : ℤ, dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + j) - dyadicNormalizedTailStateR235 dyadicShellTsumTailR235 (1 + i) = (z : ℝ) := by sorry
end PalomarCorpus.E269.AllScaleLattice
namespace PalomarCorpus.E269.CarryMechanism
open scoped BigOperators
export PalomarCorpus.E269.Shared (CofinalLocalWindowEscape leastPositiveResidue windowBase windowForcing)
def carryLiftPerturbation (base digit z : ℕ → ℤ) (n : ℕ) : ℤ := base n * z n - z (n + 1) - digit n
def carryLiftError (D : ℤ) (z carry : ℕ → ℤ) (n : ℕ) : ℤ := D * z n - carry n
def channelPrefix {G : Type*} [AddCommGroup G] (ε : ℕ → G) (N : ℕ) : G := ∑ n ∈ Finset.range N, ε n
def ChannelBlockNull {ι G : Type*} [AddCommGroup G] (jumpBase : ℕ → ι) (ε : ℕ → G) : Prop := ∀ a b, jumpBase a = jumpBase b → channelPrefix ε a = channelPrefix ε b
inductive Prime235 | two | three | five deriving DecidableEq /-- A single error bound below `2^N` contradicts any nonzero integral lift whose perturbation is block-null and vanishes at genuine `2 → 3` and `2 → 5` anchors. -/
theorem no_carryLift_of_errorBound_below_twoPow (D : ℤ) (base digit z carry : ℕ → ℤ) (jumpBase : ℕ → Prime235) (hcarry : ∀ n, carry (n + 1) = base n * carry n - D * digit n) (hchannel : Function.Surjective jumpBase) (hnull : ChannelBlockNull jumpBase (carryLiftPerturbation base digit z)) {n23 n25 : ℕ} (h23start : jumpBase n23 = .two) (h23end : jumpBase (n23 + 1) = .three) (h25start : jumpBase n25 = .two) (h25end : jumpBase (n25 + 1) = .five) (hanchor23 : carryLiftPerturbation base digit z n23 = 0) (hanchor25 : carryLiftPerturbation base digit z n25 = 0) (herror0 : carryLiftError D z carry 0 ≠ 0) (bound : ℕ → ℕ) (hbounded : ∀ n, Int.natAbs (carryLiftError D z carry n) ≤ bound n) (hbaseTwo : ∀ n, (2 : ℤ) ≤ base n) (N : ℕ) (hbelow : bound N < 2 ^ N) : False := by sorry
theorem no_unitAccurateLift_with_twoAnchors_and_firstTwoBlockNull (T0 T1 T2 T3 : ℝ) (z0 z1 z2 z3 : ℤ) (hT0 : 0 < T0 ∧ T0 < 1) (hT1 : 0 < T1 ∧ T1 < 1) (hT2 : 0 < T2 ∧ T2 < 1) (hT3 : 0 < T3 ∧ T3 < 1) (hacc0 : |(z0 : ℝ) - T0| < 1) (hacc1 : |(z1 : ℝ) - T1| < 1) (hacc2 : |(z2 : ℝ) - T2| < 1) (hacc3 : |(z3 : ℝ) - T3| < 1) (hanchor23 : 2 * z0 - z1 - 1 = 0) (hanchor25 : 2 * z2 - z3 - 1 = 0) (hfirstBlock : (2 * z0 - z1 - 1) + (3 * z1 - z2 - 1) = 0) : False := by sorry
theorem perturbation_eq_zero_of_blockNull_twoAnchors {jumpBase : ℕ → Prime235} {ε : ℕ → ℤ} (hbase : Function.Surjective jumpBase) (hnull : ChannelBlockNull jumpBase ε) {n23 n25 : ℕ} (h23start : jumpBase n23 = .two) (h23end : jumpBase (n23 + 1) = .three) (h25start : jumpBase n25 = .two) (h25end : jumpBase (n25 + 1) = .five) (hanchor23 : ε n23 = 0) (hanchor25 : ε n25 = 0) : ∀ n, ε n = 0 := by sorry
theorem carryLift_blockDefect (D : ℤ) (base digit z carry : ℕ → ℤ) (hcarry : ∀ n, carry (n + 1) = base n * carry n - D * digit n) (a b : ℕ) (hab : a ≤ b) : D * (∑ n ∈ Finset.Ico a b, carryLiftPerturbation base digit z n) = carryLiftError D z carry a - carryLiftError D z carry b + ∑ n ∈ Finset.Ico a b, (base n - 1) * carryLiftError D z carry n := by sorry
def carryResidue (B c : ℤ) : ℤ := c % B
def carryQuotient (B c : ℤ) : ℤ := c / B
def residueDigit (B base residue nextResidue : ℤ) : ℤ := (base * residue - nextResidue) / B /-- Every exact carry recurrence splits into a finite residue digit and an uncontrolled integral coboundary. -/
theorem carry_eq_residueDigit_add_coboundary (B : ℤ) (hB : 0 < B) (base carry digit : ℕ → ℤ) (hrec : ∀ n, carry (n + 1) = base n * carry n - B * digit n) : let residue := fun n => carryResidue B (carry n) let quotient := fun n => carryQuotient B (carry n) ∀ n, digit n = residueDigit B (base n) (residue n) (residue (n + 1)) + base n * quotient n - quotient (n + 1) := by sorry
theorem no_positive_reducedCarry_of_cofinalLocalWindowEscape (b m : ℕ → ℕ) (shortBound : ℕ → ℕ → ℕ) (hescape : CofinalLocalWindowEscape b m shortBound) (B : ℕ) (hBpos : 0 < B) (hBcoprime : Nat.Coprime B 30) (d : ℕ → ℤ) (hrec : ∀ n, d (n + 1) = (b n : ℤ) * d n - (B : ℤ) * (m n : ℤ)) (hpos : ∀ n, 0 < d n) (hbound : ∀ n, Int.natAbs (d n) ≤ shortBound B n) : False := by sorry
end PalomarCorpus.E269.CarryMechanism
namespace PalomarCorpus.E269.IntegralBranchPinning
open scoped BigOperators
export PalomarCorpus.E269.Shared (DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState)
theorem trueNormalizedState_pinning (a : ℕ) : trueNormalizedState a = (dyadicOrderedBlockDigit235 a : ℝ) / (dyadicBlockBase235 a : ℝ) + trueNormalizedState (a + 1) / (dyadicBlockBase235 a : ℝ) := by sorry
theorem trueNormalizedState_eq_telescope (m K : ℕ) : trueNormalizedState m = (∑ i ∈ Finset.range K, (dyadicOrderedBlockDigit235 (m + i) : ℝ) / ∏ j ∈ Finset.range (i + 1), (dyadicBlockBase235 (m + j) : ℝ)) + (threePrimeHeight 2 3 5 (2 ^ m) : ℝ) / 2 * dyadicShellTsumTailR235 (m + K) := by sorry
theorem integral_state_upward_closed {a : ℕ} {z : ℤ} (hint : trueNormalizedState a = (z : ℝ)) : ∀ n, a ≤ n → ∃ z' : ℤ, trueNormalizedState n = (z' : ℝ) := by sorry
theorem surviving_window_orbit_eq_true_state (width : ℕ → ℝ) (A : ℕ) (y : ℕ → ℝ) (hrec : ∀ n, A ≤ n → y (n + 1) = (dyadicBlockBase235 n : ℝ) * y n - (dyadicOrderedBlockDigit235 n : ℝ)) (hwin : ∀ n, A ≤ n → (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < y n ∧ y n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) (hwidth : ∀ n, A ≤ n → (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) < trueNormalizedState n ∧ trueNormalizedState n ≤ (dyadicOrderedBlockDigit235 n : ℝ) / (dyadicBlockBase235 n : ℝ) + width n) (hvanish : ∀ ε > 0, ∃ k₀ : ℕ, ∀ k, k₀ ≤ k → width (A + k) / 2 ^ k < ε) : y A = trueNormalizedState A := by sorry
end PalomarCorpus.E269.IntegralBranchPinning
namespace PalomarCorpus.E269.ThreePrimeStructure
export PalomarCorpus.E269.Shared (smooth3Val threePrimeHeight)
def threePrimeKernelQ (p q r i j k : ℕ) : ℚ := (threePrimeHeight p q r (smooth3Val p q r i j k) : ℚ)⁻¹
def smoothPrefixExponents (p q r x : ℕ) : Finset (ℕ × ℕ × ℕ) := ((Finset.range (Nat.log p x + 1)).product ((Finset.range (Nat.log q x + 1)).product (Finset.range (Nat.log r x + 1)))).filter fun e => smooth3Val p q r e.1 e.2.1 e.2.2 ≤ x
def smoothPrefixLcm (p q r x : ℕ) : ℕ := (smoothPrefixExponents p q r x).lcm fun e => smooth3Val p q r e.1 e.2.1 e.2.2
def SameThreePrimeLogCell (p q r x y : ℕ) : Prop := Nat.log p x = Nat.log p y ∧ Nat.log q x = Nat.log q y ∧ Nat.log r x = Nat.log r y
def positivePrimePowers (p count : ℕ) : Finset ℕ := (Finset.range count).image fun e => p ^ (e + 1)
def threePrimePositiveJumpSet (p q r count : ℕ) : Finset ℕ := (positivePrimePowers p count ∪ positivePrimePowers q count) ∪ positivePrimePowers r count
def smoothExponentBox (hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) := (Finset.range (hp + 1)).product ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))
def smoothPointHeight (p q r : ℕ) (e : ℕ × ℕ × ℕ) : ℕ := threePrimeHeight p q r (smooth3Val p q r e.1 e.2.1 e.2.2)
def smoothHeightFiber (p q r hp hq hr H : ℕ) : Finset (ℕ × ℕ × ℕ) := (smoothExponentBox hp hq hr).filter fun e => smoothPointHeight p q r e = H
def smoothExponentShell (p q r lo hi hp hq hr : ℕ) : Finset (ℕ × ℕ × ℕ) := ((Finset.range (hp + 1)).product ((Finset.range (hq + 1)).product (Finset.range (hr + 1)))).filter fun e => lo ≤ smooth3Val p q r e.1 e.2.1 e.2.2 ∧ smooth3Val p q r e.1 e.2.1 e.2.2 < hi /-- The literal LCM of the smooth prefix is exactly the product of the three maximal pure prime powers. -/
theorem smoothPrefixLcm_eq_threePrimeHeight {p q r x : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) (hx : x ≠ 0) : smoothPrefixLcm p q r x = threePrimeHeight p q r x := by sorry
theorem threePrimeKernelQ_eq_of_sameLogCell {p q r i j k i' j' k' : ℕ} (hcell : SameThreePrimeLogCell p q r (smooth3Val p q r i j k) (smooth3Val p q r i' j' k')) : threePrimeKernelQ p q r i j k = threePrimeKernelQ p q r i' j' k' := by sorry
theorem threePrimePositiveJumpSet_card {p q r count : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) : (threePrimePositiveJumpSet p q r count).card = 3 * count := by sorry
theorem finiteSmoothKernelSum_groupedByHeight (p q r hp hq hr : ℕ) : (∑ e ∈ smoothExponentBox hp hq hr, threePrimeKernelQ p q r e.1 e.2.1 e.2.2) = ∑ H ∈ (smoothExponentBox hp hq hr).image (smoothPointHeight p q r), (smoothHeightFiber p q r hp hq hr H).card • ((H : ℚ)⁻¹) := by sorry
theorem smoothExponentShell_card_quadratic {p q r lo hi hp hq hr j : ℕ} (hrPos : 0 < r) (hwidth : hi ≤ r * lo) (hpq : hp ≤ hq) (hqr : hq ≤ hr) (hsum : hp + hq + hr = j) : 9 * (smoothExponentShell p q r lo hi hp hq hr).card ≤ (j + 3) ^ 2 := by sorry
theorem kernel_235_minor_eq_neg_one_fifteen : threePrimeKernelQ 2 3 5 0 0 0 * threePrimeKernelQ 2 3 5 1 1 0 - threePrimeKernelQ 2 3 5 1 0 0 * threePrimeKernelQ 2 3 5 0 1 0 = -(1 / 15 : ℚ) := by sorry
def NoIntegerOrbit (α : ℝ) : Prop := ∀ n : ℕ, 0 < n → Int.fract ((n : ℝ) * α) ≠ 0 /-- Generators `1 < p, q, r` whose logarithmic ratios `Real.logb r p` and `Real.logb r q` have no integer orbit force nonsingular kernel minors of every order, simultaneously in every third-coordinate layer. -/
theorem exists_uniform_nonsingular_threePrimeKernel_minor {p q r : ℕ} (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) (hα : NoIntegerOrbit (Real.logb r p)) (hβ : NoIntegerOrbit (Real.logb r q)) (n : ℕ) : ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧ ∀ k : ℕ, (Matrix.det fun a b : Fin n => threePrimeKernelQ p q r (I a) (J b) k) ≠ 0 := by sorry
theorem threePrimeKernel_infiniteRank_and_noFiniteSeparation {p q r : ℕ} (hp : p.Prime) (hq : q.Prime) (hr : r.Prime) (hpr : p ≠ r) (hqr : q ≠ r) : (∀ n : ℕ, ∃ I J : Fin n → ℕ, Function.Injective I ∧ Function.Injective J ∧ ∀ k : ℕ, (Matrix.det fun a b : Fin n => threePrimeKernelQ p q r (I a) (J b) k) ≠ 0) ∧ (∀ d : ℕ, ¬ ∃ (f : Fin d → ℕ → ℚ) (G : Fin d → ℕ → ℕ → ℚ), ∀ i j k, threePrimeKernelQ p q r i j k = ∑ l : Fin d, f l i * G l j k) := by sorry
end PalomarCorpus.E269.ThreePrimeStructure
namespace PalomarCorpus.E269.WindowEscapeEquivalence
open scoped BigOperators
export PalomarCorpus.E269.Shared (CofinalLocalWindowEscape DyadicInternalPower dyadicBeforeThresholdCount235 dyadicBlockBase235 dyadicNormalizedTailStateR235 dyadicOrderedBlockDigit235 dyadicShellMassQ235 dyadicShellMassR235 dyadicShellTsumTailR235 dyadicSmoothShell235 leastPositiveResidue smooth3Val strictSmoothExponents strictSmoothShell threePrimeHeight trueNormalizedState windowBase windowForcing)
def bridgeWidth (n : ℕ) : ℕ := 90 * (n + 1) ^ 2 /-- The producer stated for the actual radix word, the actual ordered digit and the short bound `B · 90 (n+1)^2`. -/
def ActualCofinalLocalWindowEscape : Prop := CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun B n => B * bridgeWidth n) /-- The actual cofinal local-window escape is equivalent to irrationality of the `{2,3,5}` running-LCM value. -/
theorem actualCofinalLocalWindowEscape_iff_irrational_value : ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 0) := by sorry
theorem actualCofinalLocalWindowEscape_iff : ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 1) := by sorry
theorem cofinalLocalWindowEscape_of_irrational (h : Irrational (dyadicShellTsumTailR235 1)) : ActualCofinalLocalWindowEscape := by sorry
theorem cofinalLocalWindowEscape_of_irrational_of_quadratic (h : Irrational (dyadicShellTsumTailR235 1)) (sb : ℕ → ℕ → ℕ) (c : ℕ → ℕ) (hsb : ∀ B n, sb B n ≤ c B * (n + 1) ^ 2) : CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 sb := by sorry
theorem exists_reducedCarry_of_value_eq_rat {p q : ℤ} (hq : 0 < q) (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) : ∃ (B a₀ : ℕ) (d : ℕ → ℤ), 0 < B ∧ Nat.Coprime B 30 ∧ (∀ n, a₀ ≤ n → d (n + 1) = (dyadicBlockBase235 n : ℤ) * d n - (B : ℤ) * (dyadicOrderedBlockDigit235 n : ℤ)) ∧ (∀ n, a₀ ≤ n → 0 < d n) ∧ (∀ n, a₀ ≤ n → Int.natAbs (d n) ≤ B * bridgeWidth n) := by sorry
theorem trueNormalizedState_window (lo len : ℕ) : trueNormalizedState (lo + len) = ((windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len : ℤ) : ℝ) * trueNormalizedState lo - ((windowForcing (fun n => (dyadicBlockBase235 n : ℤ)) (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len : ℤ) : ℝ) := by sorry
theorem near_integer_of_residue_le_general (B lo len K : ℕ) (hB : 0 < B) (hKle : B * bridgeWidth (lo + len) ≤ K) (hres : leastPositiveResidue (Int.natAbs (windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len)) (-((B : ℤ) * windowForcing (fun n => (dyadicBlockBase235 n : ℤ)) (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len)) ≤ K) : ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)| ≤ ((K : ℕ) : ℝ) / 2 ^ len := by sorry
theorem exists_pow_gt_quadratic (c lo : ℕ) : ∃ len : ℕ, 0 < len ∧ c * (lo + len + 1) ^ 2 < 2 ^ len := by sorry
end PalomarCorpus.E269.WindowEscapeEquivalence
