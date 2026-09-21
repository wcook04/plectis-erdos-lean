import Mathlib.Algebra.GCDMonoid.Finset
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Find
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.ZMod.Basic
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.NumberTheory.Bertrand
import Mathlib.NumberTheory.Multiplicity
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.NumberTheory.TsumDivisorsAntidiagonal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Eval
import Mathlib.RingTheory.Polynomial.Cyclotomic.Expand
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.InfiniteSum.Ring
import Erdos257PeriodNoncollapse.GapFareyBound
import Erdos257PeriodNoncollapse.MersenneLambertLadder
import Erdos257PeriodNoncollapse.GeometricCoprimality
import Erdos257PeriodNoncollapse.GcdMomentCalculus
import Erdos257PeriodNoncollapse.SternBrocotRunGeometry
import Erdos257PeriodNoncollapse.TotientTailPeriodKiller
import Erdos257PeriodNoncollapse.CarrySurvivorExtinction
import Erdos257PeriodNoncollapse.LcmDiagonalReduction
import Erdos257PeriodNoncollapse.LcmConeFlatness
import Erdos257PeriodNoncollapse.LcmConeNonflat
import Erdos257PeriodNoncollapse.CertificateKernel

/-
The paper repository's copy of this module does not declare the results below; they were proved in
this corpus. A shim can only publish a name the library has, so this module keeps them, and keeps them
exactly as they were written: it is the corpus module with every declaration the library already carries
removed, and the shim imported in their place. No statement, hypothesis, proof or name is changed here.
-/

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos257PeriodNoncollapse

/-- **Pointwise reduced-denominator saturation.**  A rational value forces
the actual reduced denominator `Qₖ` of every prefix to satisfy
`b ^ a(k) ≤ 4 * den(q) * Qₖ`.  This is the quantitative lower bound hidden
behind the subsequence irrationality criterion, not merely its asymptotic
contrapositive. -/
theorem rational_erdosSum_prefix_denominator_saturation
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (q : ℚ)
    (hq : (∑' j, (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) = (q : ℝ))
    (k : ℕ) :
    (b : ℝ) ^ (a k) ≤
      4 * (q.den : ℝ) *
        ((finiteErdosSum ((Finset.range k).image a) b).den : ℝ) := by
  set u : ℚ := finiteErdosSum ((Finset.range k).image a) b with hu
  have hfrac :
      (1 : ℝ) / ((q.den : ℝ) * (u.den : ℝ))
        ≤ 4 / ((b : ℝ) ^ (a k)) := by
    calc
      (1 : ℝ) / ((q.den : ℝ) * (u.den : ℝ))
          ≤ ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + k)) - 1) := by
            simpa [hu] using
              rational_erdosSum_prefix_tail_lower b hb a ha ha0 q hq k
      _ ≤ 4 * ((1 : ℝ) / b) ^ (a k) :=
            erdos_tail_le b hb a ha ha0 k
      _ = 4 / ((b : ℝ) ^ (a k)) := by
            rw [div_pow, one_pow]
            ring
  have hden_pos : (0 : ℝ) < (q.den : ℝ) * (u.den : ℝ) := by positivity
  have hb_pos : (0 : ℝ) < (b : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hb)
  have hpow_pos : (0 : ℝ) < (b : ℝ) ^ (a k) := pow_pos hb_pos _
  rw [div_le_div_iff₀ hden_pos hpow_pos] at hfrac
  simpa [hu, mul_assoc] using hfrac

/-- **Rational-support saturation package.**  At every nonempty prefix, a
hypothetical rational Erdős sum forces one and the same reduced denominator
to be exponentially large at the next support scale, to have exact
multiplicative order equal to the exponent lcm, and to divide the lcm of the
displayed Mersenne term denominators. -/
theorem rational_erdosSum_prefix_saturation_order_lcm
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (q : ℚ)
    (hq : (∑' j, (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) = (q : ℝ))
    (k : ℕ) (hk : 0 < k) :
    (b : ℝ) ^ (a k) ≤
        4 * (q.den : ℝ) *
          ((finiteErdosSum ((Finset.range k).image a) b).den : ℝ) ∧
      orderOf
          (ZMod.unitOfCoprime b
            (coprime_base_den_finiteErdosSum ((Finset.range k).image a) b
              (zero_not_mem_image_range_of_strictMono_pos a ha ha0 k) hb))
        = ((Finset.range k).image a).lcm id ∧
      (finiteErdosSum ((Finset.range k).image a) b).den ∣
        ((Finset.range k).image a).lcm (fun n => b ^ n - 1) := by
  have hF : ((Finset.range k).image a).Nonempty :=
    ⟨a 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hk, rfl⟩⟩
  have h0 := zero_not_mem_image_range_of_strictMono_pos a ha ha0 k
  exact ⟨
    rational_erdosSum_prefix_denominator_saturation b hb a ha ha0 q hq k,
    finite_period_noncollapse_rat_den ((Finset.range k).image a) b hF h0 hb,
    den_finiteErdosSum_dvd_termDenominatorLcm
      ((Finset.range k).image a) b h0 hb⟩

/-- **Exact reduced-denominator subsequence criterion.**  Let `Qₖ` be the
actual reduced denominator of the finite support sum through any selected
prefix `κ k`.  If `Qₖ · b ^ (-a (κ k))` tends to zero, then the infinite
Erdős support sum is irrational.

This is strictly more flexible than the exponent-lcm criterion below: it uses
`Rat.den` itself rather than an upper common denominator, and it only needs a
successful subsequence of prefixes rather than a full-sequence gap law. -/
theorem irrational_erdosSum_of_reducedDenominator_subsequence_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (κ : ℕ → ℕ)
    (hgap : Tendsto
      (fun k =>
        ((finiteErdosSum ((Finset.range (κ k)).image a) b).den : ℝ) *
          ((1 : ℝ) / b) ^ (a (κ k)))
      atTop (nhds 0)) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := by
  have hsum : Summable (fun j => (1 : ℝ) / ((b : ℝ) ^ (a j) - 1)) :=
    summable_erdos_term b hb a ha ha0
  set x : ℝ := ∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1) with hx
  set u : ℕ → ℚ :=
    fun k => finiteErdosSum ((Finset.range (κ k)).image a) b with hu
  have hval : ∀ k, x - ((u k : ℚ) : ℝ)
      = ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + κ k)) - 1) := by
    intro k
    have hsplit := hsum.sum_add_tsum_nat_add (κ k)
    have hcast := finiteErdosSum_image_range_cast b a ha (κ k)
    have huk : ((u k : ℚ) : ℝ)
        = ∑ i ∈ Finset.range (κ k), (1 : ℝ) / ((b : ℝ) ^ (a i) - 1) := by
      rw [hu]
      exact hcast
    rw [huk]
    linarith
  have hne : ∀ k, ((u k : ℚ) : ℝ) ≠ x := by
    intro k hEq
    have h1 := hval k
    rw [hEq] at h1
    have h2 := erdos_tail_pos b hb a ha ha0 (κ k)
    simp only [sub_self] at h1
    linarith
  apply irrational_of_den_mul_abs_sub_tendsto_zero
    (Filter.Eventually.of_forall hne)
  have hlim : Tendsto
      (fun k =>
        4 * (((u k).den : ℝ) * ((1 : ℝ) / b) ^ (a (κ k))))
      atTop (nhds 0) := by
    have hgap' : Tendsto
        (fun k => ((u k).den : ℝ) * ((1 : ℝ) / b) ^ (a (κ k)))
        atTop (nhds 0) := by
      simpa [hu] using hgap
    simpa using hgap'.const_mul (4 : ℝ)
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun k =>
      mul_nonneg (Nat.cast_nonneg _) (abs_nonneg _))
    (Filter.Eventually.of_forall fun k => ?_) hlim
  have htail_pos := erdos_tail_pos b hb a ha ha0 (κ k)
  have htail_le := erdos_tail_le b hb a ha ha0 (κ k)
  have habs : |x - ((u k : ℚ) : ℝ)|
      = ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + κ k)) - 1) := by
    rw [hval k]
    exact abs_of_pos htail_pos
  calc
    ((u k).den : ℝ) * |x - ((u k : ℚ) : ℝ)|
        = ((u k).den : ℝ) *
            ∑' i, (1 : ℝ) / ((b : ℝ) ^ (a (i + κ k)) - 1) := by
              rw [habs]
    _ ≤ ((u k).den : ℝ) * (4 * ((1 : ℝ) / b) ^ (a (κ k))) := by
          exact mul_le_mul_of_nonneg_left htail_le (Nat.cast_nonneg _)
    _ = 4 * (((u k).den : ℝ) * ((1 : ℝ) / b) ^ (a (κ k))) := by ring

/-- **Mersenne-term-lcm subsequence criterion.**  The reduced denominator
criterion follows already when the lcm of the *displayed term denominators*
`b ^ a(i) - 1` has sufficiently small product with the next geometric scale
along any sequence of prefixes.  This is sharper than replacing that lcm by
the larger common denominator `b ^ lcm(a(i)) - 1`. -/
theorem irrational_erdosSum_of_termDenominatorLcm_subsequence_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (κ : ℕ → ℕ)
    (hgap : Tendsto
      (fun k =>
        ((((Finset.range (κ k)).image a).lcm (fun n => b ^ n - 1) : Nat) : ℝ) *
          ((1 : ℝ) / b) ^ (a (κ k)))
      atTop (nhds 0)) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := by
  apply irrational_erdosSum_of_reducedDenominator_subsequence_gap
    b hb a ha ha0 κ
  apply squeeze_zero'
    (Filter.Eventually.of_forall fun k =>
      mul_nonneg (Nat.cast_nonneg _) (by positivity))
    (Filter.Eventually.of_forall fun k => ?_) hgap
  have h0F : 0 ∉ (Finset.range (κ k)).image a := by
    intro hmem
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
    have hai : 1 ≤ a i := le_trans ha0 (ha.monotone (Nat.zero_le i))
    omega
  have hL_ne :
      ((Finset.range (κ k)).image a).lcm (fun n => b ^ n - 1) ≠ 0 := by
    rw [Ne, Finset.lcm_eq_zero_iff]
    rintro ⟨n, hn, hzero⟩
    have hn0 : n ≠ 0 := fun hnEq => h0F (hnEq ▸ hn)
    have hpos := pow_sub_one_pos_of_ne_zero b n hb hn0
    omega
  have hdvd := den_finiteErdosSum_dvd_termDenominatorLcm
    ((Finset.range (κ k)).image a) b h0F hb
  have hden_le :
      ((finiteErdosSum ((Finset.range (κ k)).image a) b).den : ℝ) ≤
        ((((Finset.range (κ k)).image a).lcm
          (fun n => b ^ n - 1) : Nat) : ℝ) := by
    exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hL_ne) hdvd
  exact mul_le_mul_of_nonneg_right hden_le (by positivity)

/-- Full-sequence wrapper for
`irrational_erdosSum_of_reducedDenominator_subsequence_gap`. -/
theorem irrational_erdosSum_of_reducedDenominator_gap
    (b : ℕ) (hb : 2 ≤ b) (a : ℕ → ℕ) (ha : StrictMono a) (ha0 : 1 ≤ a 0)
    (hgap : Tendsto
      (fun k =>
        ((finiteErdosSum ((Finset.range k).image a) b).den : ℝ) *
          ((1 : ℝ) / b) ^ (a k))
      atTop (nhds 0)) :
    Irrational (∑' k, (1 : ℝ) / ((b : ℝ) ^ (a k) - 1)) := by
  simpa using
    irrational_erdosSum_of_reducedDenominator_subsequence_gap
      b hb a ha ha0 id hgap

end Erdos257PeriodNoncollapse
