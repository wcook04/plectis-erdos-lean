-- Generated direct-prime emitted certificates, part 2 of 16 (10 certificates).
import Erdos249257.CertificateKernel
import Mathlib.Tactic.NormNum.Prime
import Erdos249257.GeneratedCertificates.Part00

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F105_A497_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (105 : Nat).factorization.support) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have hsupport :
      (105 : Nat).factorization.support = ({3, 5, 7} : Finset Nat) := by
    rw [Nat.support_factorization]
    rw [show (105 : Nat) = 3 * (5 * (7)) by decide]
    rw [Nat.primeFactors_mul (by decide) (by decide)]
    rw [Nat.primeFactors_mul (by decide) (by decide)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 3)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 5)]
    rw [Nat.Prime.primeFactors (by decide : Nat.Prime 7)]
    rfl
  rw [hsupport] at hp
  simpa using hp

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A497_p3_prime_witness :
    PrimeComponentWitness 105 497 2 3 7 := by
  refine ⟨(by decide : Nat.Prime 7), ?_, ?_⟩
  · have hquot : primeComponentQuotient 2 105 3 = 1180591620751771041793 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 2 105 3 = 1180591620751771041793 := by decide
    rw [hquot]
    have hfactor : (1180591620751771041793 : Nat).factorization 7 = 2 := by
      rw [show (1180591620751771041793 : Nat) = 7 ^ 2 * 24093706545954511057 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      change (7 ^ 2 : Nat).factorization 7 + (24093706545954511057 : Nat).factorization 7 = 2
      have hleft : (7 ^ 2 : Nat).factorization 7 = 2 :=
        Nat.factorization_pow_self (by decide : Nat.Prime 7)
      have hright : (24093706545954511057 : Nat).factorization 7 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 24093706545954511057)
      rw [hleft, hright]
    rw [hfactor]
    have hA_factor : (497 : Nat).factorization 7 = 1 := by
      rw [show (497 : Nat) = 7 * 71 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 7),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 71),
      ]
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F105_A497_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 497 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F105_A497_p3_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A497_p5_prime_witness :
    PrimeComponentWitness 105 497 2 5 31 := by
  have hquot : primeComponentQuotient 2 105 5 = 19342822337210501698682881 := by decide
  have hq : Nat.Prime 31 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 31 ∣ 497)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A497_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 497 2 5 := by
  exact Or.inr (Or.inr ⟨31, concrete_generated_b2_F105_A497_p5_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A497_p7_prime_witness :
    PrimeComponentWitness 105 497 2 7 127 := by
  have hquot : primeComponentQuotient 2 105 7 = 1237977819370199922113544193 := by decide
  have hq : Nat.Prime 127 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 127 ∣ 497)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A497_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 497 2 7 := by
  exact Or.inr (Or.inr ⟨127, concrete_generated_b2_F105_A497_p7_prime_witness⟩)

def emittedCertificate_b2_L105_A497 :
    EmittedCertificateTable 105 497 2 where
  rows := ({3, 5, 7} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F105_A497_factorization_support_cases hp with rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A497_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A497_p5_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A497_p7_prime_witness

set_option maxRecDepth 10000 in
theorem orderOf_b2_mod81619354541857828667795779823_eq_105_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 81619354541857828667795779823)) = 105 := by
  let hcop : Nat.Coprime 2 81619354541857828667795779823 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 105 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 105 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 81619354541857828667795779823)ˣ) :
          ZMod 81619354541857828667795779823) ^ 105) =
        (1 : ZMod 81619354541857828667795779823)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    105 497 40564819207303340847894502572031 81619354541857828667795779823 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L105_A497

theorem concrete_lifted_b2_F105_A75047_from_A497_mul151_p3_prime_witness :
    PrimeComponentWitness 105 75047 2 3 7 := by
  rw [show (75047 : Nat) = 497 * 151 by decide]
  exact PrimeComponentWitness.mul_right_of_factorization_eq_zero
    concrete_generated_b2_F105_A497_p3_prime_witness
    (by decide : (497 : Nat) ≠ 0)
    (by decide : (151 : Nat) ≠ 0)
    (Nat.factorization_eq_zero_of_not_dvd
      (by decide : ¬ 7 ∣ 151))

theorem concrete_lifted_b2_F105_A75047_from_A497_mul151_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 75047 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b2_F105_A75047_from_A497_mul151_p3_prime_witness⟩)

theorem concrete_lifted_b2_F105_A75047_from_A497_mul151_p5_prime_witness :
    PrimeComponentWitness 105 75047 2 5 31 := by
  have hquot : primeComponentQuotient 2 105 5 = 19342822337210501698682881 := by decide
  have hq : Nat.Prime 31 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 31 ∣ 75047)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b2_F105_A75047_from_A497_mul151_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 75047 2 5 := by
  exact Or.inr (Or.inr ⟨31, concrete_lifted_b2_F105_A75047_from_A497_mul151_p5_prime_witness⟩)

theorem concrete_lifted_b2_F105_A75047_from_A497_mul151_p7_prime_witness :
    PrimeComponentWitness 105 75047 2 7 127 := by
  have hquot : primeComponentQuotient 2 105 7 = 1237977819370199922113544193 := by decide
  have hq : Nat.Prime 127 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 127 ∣ 75047)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b2_F105_A75047_from_A497_mul151_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 75047 2 7 := by
  exact Or.inr (Or.inr ⟨127, concrete_lifted_b2_F105_A75047_from_A497_mul151_p7_prime_witness⟩)

theorem concrete_generated_b3_F5_A11_p5_prime_witness :
    PrimeComponentWitness 5 11 3 5 11 := by
  refine ⟨(by decide : Nat.Prime 11), ?_, ?_⟩
  · have hquot : primeComponentQuotient 3 5 5 = 121 := by decide
    rw [hquot]
    decide
  · have hquot : primeComponentQuotient 3 5 5 = 121 := by decide
    rw [hquot]
    have hfactor : (121 : Nat).factorization 11 = 2 := by
      rw [show (121 : Nat) = 11 ^ 2 * 1 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      change (11 ^ 2 : Nat).factorization 11 + (1 : Nat).factorization 11 = 2
      have hleft : (11 ^ 2 : Nat).factorization 11 = 2 :=
        Nat.factorization_pow_self (by decide : Nat.Prime 11)
      have hright : (1 : Nat).factorization 11 = 0 :=
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 1)
      rw [hleft, hright]
    rw [hfactor]
    have hA_factor : (11 : Nat).factorization 11 = 1 :=
      Nat.Prime.factorization_self (by decide : Nat.Prime 11)
    rw [hA_factor]
    decide

theorem concrete_generated_b3_F5_A11_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 5 11 3 5 := by
  exact Or.inr (Or.inr ⟨11, concrete_generated_b3_F5_A11_p5_prime_witness⟩)

def emittedCertificate_b3_L5_A11 :
    EmittedCertificateTable 5 11 3 where
  rows := ({5} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b3_F5_factorization_support_cases hp with rfl
    simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b3_F5_A11_p5_prime_witness

theorem orderOf_b3_mod22_eq_5_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 3
      (by decide : Nat.Coprime 3 22)) = 5 := by
  let hcop : Nat.Coprime 3 22 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 3 hcop) ∣ 5 := by
    have hpow_unit : (ZMod.unitOfCoprime 3 hcop) ^ 5 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 3 hcop : (ZMod 22)ˣ) : ZMod 22) ^ 5) =
        (1 : ZMod 22)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    5 11 242 22 3 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 3 hcop)) 3 (by decide))
    emittedCertificate_b3_L5_A11

theorem concrete_lifted_b10_F6_A33_from_A3_mul11_p2_prime_witness :
    PrimeComponentWitness 6 33 10 2 7 := by
  have hquot : primeComponentQuotient 10 6 2 = 1001 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 33)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b10_F6_A33_from_A3_mul11_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 33 10 2 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b10_F6_A33_from_A3_mul11_p2_prime_witness⟩)

theorem concrete_lifted_b10_F6_A33_from_A3_mul11_p3_prime_witness :
    PrimeComponentWitness 6 33 10 3 7 := by
  have hquot : primeComponentQuotient 10 6 3 = 10101 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 33)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b10_F6_A33_from_A3_mul11_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 33 10 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b10_F6_A33_from_A3_mul11_p3_prime_witness⟩)

theorem concrete_generated_b12_F12_A55_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A55_p2_prime_witness :
    PrimeComponentWitness 12 55 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 55)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A55_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 55 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A55_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A55_p3_prime_witness :
    PrimeComponentWitness 12 55 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 55)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A55_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 55 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A55_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A55 :
    EmittedCertificateTable 12 55 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A55_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A55_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A55_p3_prime_witness

theorem orderOf_b12_mod162110917241_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 162110917241)) = 12 := by
  let hcop : Nat.Coprime 12 162110917241 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 162110917241)ˣ) :
          ZMod 162110917241) ^ 12) =
        (1 : ZMod 162110917241)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 55 8916100448255 162110917241 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A55

theorem concrete_generated_b12_F12_A1595_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A1595_p2_prime_witness :
    PrimeComponentWitness 12 1595 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 1595)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1595_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1595 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A1595_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A1595_p3_prime_witness :
    PrimeComponentWitness 12 1595 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 1595)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1595_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1595 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A1595_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1595 :
    EmittedCertificateTable 12 1595 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1595_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1595_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1595_p3_prime_witness

theorem orderOf_b12_mod5590031629_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 5590031629)) = 12 := by
  let hcop : Nat.Coprime 12 5590031629 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 5590031629)ˣ) :
          ZMod 5590031629) ^ 12) =
        (1 : ZMod 5590031629)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1595 8916100448255 5590031629 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1595

theorem concrete_generated_b12_F12_A20881_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A20881_p2_prime_witness :
    PrimeComponentWitness 12 20881 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 20881)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A20881_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 20881 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A20881_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A20881_p3_prime_witness :
    PrimeComponentWitness 12 20881 12 3 20593 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 20881)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A20881_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 20881 12 3 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A20881_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A20881 :
    EmittedCertificateTable 12 20881 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A20881_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A20881_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A20881_p3_prime_witness

theorem orderOf_b12_mod426995855_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 426995855)) = 12 := by
  let hcop : Nat.Coprime 12 426995855 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 426995855)ˣ) :
          ZMod 426995855) ^ 12) =
        (1 : ZMod 426995855)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 20881 8916100448255 426995855 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A20881

theorem concrete_generated_b12_F12_A432535_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A432535_p2_prime_witness :
    PrimeComponentWitness 12 432535 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 432535)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A432535_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 432535 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A432535_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A432535_p3_prime_witness :
    PrimeComponentWitness 12 432535 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 432535)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A432535_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 432535 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A432535_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A432535 :
    EmittedCertificateTable 12 432535 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A432535_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A432535_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A432535_p3_prime_witness

theorem orderOf_b12_mod20613593_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 20613593)) = 12 := by
  let hcop : Nat.Coprime 12 20613593 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 20613593)ˣ) :
          ZMod 20613593) ^ 12) =
        (1 : ZMod 20613593)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 432535 8916100448255 20613593 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A432535

theorem concrete_generated_b12_F12_A551551_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A551551_p2_prime_witness :
    PrimeComponentWitness 12 551551 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 551551)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A551551_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 551551 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A551551_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A551551_p3_prime_witness :
    PrimeComponentWitness 12 551551 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 551551)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A551551_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 551551 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A551551_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A551551 :
    EmittedCertificateTable 12 551551 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A551551_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A551551_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A551551_p3_prime_witness

theorem orderOf_b12_mod16165505_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 16165505)) = 12 := by
  let hcop : Nat.Coprime 12 16165505 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 16165505)ˣ) :
          ZMod 16165505) ^ 12) =
        (1 : ZMod 16165505)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 551551 8916100448255 16165505 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A551551

theorem concrete_generated_b12_F12_A13694345_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A13694345_p2_prime_witness :
    PrimeComponentWitness 12 13694345 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 13694345)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A13694345_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 13694345 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A13694345_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A13694345_p3_prime_witness :
    PrimeComponentWitness 12 13694345 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 13694345)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A13694345_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 13694345 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A13694345_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A13694345 :
    EmittedCertificateTable 12 13694345 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A13694345_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A13694345_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A13694345_p3_prime_witness

theorem orderOf_b12_mod651079_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 651079)) = 12 := by
  let hcop : Nat.Coprime 12 651079 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 651079)ˣ) : ZMod 651079) ^ 12) =
        (1 : ZMod 651079)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 13694345 8916100448255 651079 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A13694345

theorem concrete_generated_b12_F12_A1244743885_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (12 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 12 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 12 := Nat.le_of_dvd (by decide : 0 < 12) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact False.elim ((by decide : ¬ 11 ∣ 12) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)

theorem concrete_generated_b12_F12_A1244743885_p2_prime_witness :
    PrimeComponentWitness 12 1244743885 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 1244743885)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1244743885_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1244743885 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A1244743885_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A1244743885_p3_prime_witness :
    PrimeComponentWitness 12 1244743885 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 1244743885)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1244743885_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1244743885 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A1244743885_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1244743885 :
    EmittedCertificateTable 12 1244743885 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1244743885_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1244743885_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1244743885_p3_prime_witness

theorem orderOf_b12_mod7163_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 7163)) = 12 := by
  let hcop : Nat.Coprime 12 7163 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 7163)ˣ) : ZMod 7163) ^ 12) =
        (1 : ZMod 7163)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1244743885 8916100448255 7163 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1244743885

end Erdos249257
