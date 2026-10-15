-- Generated direct-prime emitted certificates, part 7 of 16 (11 certificates).
import Erdos249257.CertificateKernel
import Mathlib.Tactic.NormNum.Prime
import Erdos249257.GeneratedCertificates.Part00

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F33_A7_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (33 : Nat).factorization.support) :
    p = 3 ∨ p = 11 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 33 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 33 := Nat.le_of_dvd (by decide : 0 < 33) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact False.elim ((by decide : ¬ 2 ∣ 33) hp_dvd)
  · exact Or.inl rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)
  · exact False.elim ((by decide : ¬ 7 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 8) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 9) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 10) hp_prime)
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 12) hp_prime)
  · exact False.elim ((by decide : ¬ 13 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 14) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 15) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 16) hp_prime)
  · exact False.elim ((by decide : ¬ 17 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 18) hp_prime)
  · exact False.elim ((by decide : ¬ 19 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 20) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 21) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 22) hp_prime)
  · exact False.elim ((by decide : ¬ 23 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 24) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 25) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 26) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 27) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 28) hp_prime)
  · exact False.elim ((by decide : ¬ 29 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 30) hp_prime)
  · exact False.elim ((by decide : ¬ 31 ∣ 33) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 32) hp_prime)
  · exact False.elim ((by decide : ¬ Nat.Prime 33) hp_prime)

theorem concrete_generated_b2_F33_A7_p3_prime_witness :
    PrimeComponentWitness 33 7 2 3 599479 := by
  have hquot : primeComponentQuotient 2 33 3 = 4196353 := by decide
  have hq : Nat.Prime 599479 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 599479 ∣ 7)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F33_A7_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 7 2 3 := by
  exact Or.inr (Or.inr ⟨599479, concrete_generated_b2_F33_A7_p3_prime_witness⟩)

theorem concrete_generated_b2_F33_A7_p11_prime_witness :
    PrimeComponentWitness 33 7 2 11 23 := by
  have hquot : primeComponentQuotient 2 33 11 = 1227133513 := by decide
  have hq : Nat.Prime 23 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 23 ∣ 7)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F33_A7_p11_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 33 7 2 11 := by
  exact Or.inr (Or.inr ⟨23, concrete_generated_b2_F33_A7_p11_prime_witness⟩)

def emittedCertificate_b2_L33_A7 :
    EmittedCertificateTable 33 7 2 where
  rows := ({3, 11} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F33_A7_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F33_A7_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F33_A7_p11_prime_witness

theorem orderOf_b2_mod1227133513_eq_33_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 1227133513)) = 33 := by
  let hcop : Nat.Coprime 2 1227133513 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 33 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 33 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 1227133513)ˣ) :
          ZMod 1227133513) ^ 33) =
        (1 : ZMod 1227133513)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    33 7 8589934591 1227133513 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L33_A7

theorem concrete_lifted_b4_F12_A15_from_A3_mul5_p2_prime_witness :
    PrimeComponentWitness 12 15 4 2 17 := by
  have hquot : primeComponentQuotient 4 12 2 = 4097 := by decide
  have hq : Nat.Prime 17 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 17 ∣ 15)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b4_F12_A15_from_A3_mul5_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 15 4 2 := by
  exact Or.inr (Or.inr ⟨17, concrete_lifted_b4_F12_A15_from_A3_mul5_p2_prime_witness⟩)

theorem concrete_lifted_b4_F12_A15_from_A3_mul5_p3_prime_witness :
    PrimeComponentWitness 12 15 4 3 7 := by
  have hquot : primeComponentQuotient 4 12 3 = 65793 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 15)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b4_F12_A15_from_A3_mul5_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 15 4 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_lifted_b4_F12_A15_from_A3_mul5_p3_prime_witness⟩)

theorem concrete_generated_b4_F12_A273_factorization_support_cases
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

theorem concrete_generated_b4_F12_A273_p2_prime_witness :
    PrimeComponentWitness 12 273 4 2 17 := by
  have hquot : primeComponentQuotient 4 12 2 = 4097 := by decide
  have hq : Nat.Prime 17 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 17 ∣ 273)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A273_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 273 4 2 := by
  exact Or.inr (Or.inr ⟨17, concrete_generated_b4_F12_A273_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b4_F12_A273_p3_prime_witness :
    PrimeComponentWitness 12 273 4 3 241 := by
  have hquot : primeComponentQuotient 4 12 3 = 65793 := by decide
  have hq : Nat.Prime 241 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 241 ∣ 273)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A273_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 273 4 3 := by
  exact Or.inr (Or.inr ⟨241, concrete_generated_b4_F12_A273_p3_prime_witness⟩)

def emittedCertificate_b4_L12_A273 :
    EmittedCertificateTable 12 273 4 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b4_F12_A273_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A273_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A273_p3_prime_witness

theorem orderOf_b4_mod61455_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 4
      (by decide : Nat.Coprime 4 61455)) = 12 := by
  let hcop : Nat.Coprime 4 61455 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 4 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 4 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 4 hcop : (ZMod 61455)ˣ) : ZMod 61455) ^ 12) =
        (1 : ZMod 61455)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 273 16777215 61455 4 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 4 hcop)) 4 (by decide))
    emittedCertificate_b4_L12_A273

theorem concrete_lifted_b6_F12_A2015_from_A403_mul5_p2_prime_witness :
    PrimeComponentWitness 12 2015 6 2 37 := by
  have hquot : primeComponentQuotient 6 12 2 = 46657 := by decide
  have hq : Nat.Prime 37 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 37 ∣ 2015)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b6_F12_A2015_from_A403_mul5_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2015 6 2 := by
  exact Or.inr (Or.inr ⟨37, concrete_lifted_b6_F12_A2015_from_A403_mul5_p2_prime_witness⟩)

theorem concrete_lifted_b6_F12_A2015_from_A403_mul5_p3_prime_witness :
    PrimeComponentWitness 12 2015 6 3 43 := by
  have hquot : primeComponentQuotient 6 12 3 = 1680913 := by decide
  have hq : Nat.Prime 43 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 43 ∣ 2015)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b6_F12_A2015_from_A403_mul5_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2015 6 3 := by
  exact Or.inr (Or.inr ⟨43, concrete_lifted_b6_F12_A2015_from_A403_mul5_p3_prime_witness⟩)

theorem concrete_generated_b10_F6_A273_factorization_support_cases
    {p : Nat}
    (hp : p ∈ (6 : Nat).factorization.support) :
    p = 2 ∨ p = 3 := by
  rw [Nat.support_factorization] at hp
  have hp_prime : Nat.Prime p := Nat.prime_of_mem_primeFactors hp
  have hp_dvd : p ∣ 6 := (Nat.mem_primeFactors.mp hp).2.1
  have hp_le : p ≤ 6 := Nat.le_of_dvd (by decide : 0 < 6) hp_dvd
  have hp_pos : 0 < p := hp_prime.pos
  interval_cases p
  · exact False.elim ((by decide : ¬ Nat.Prime 1) hp_prime)
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact False.elim ((by decide : ¬ Nat.Prime 4) hp_prime)
  · exact False.elim ((by decide : ¬ 5 ∣ 6) hp_dvd)
  · exact False.elim ((by decide : ¬ Nat.Prime 6) hp_prime)

theorem concrete_generated_b10_F6_A273_p2_prime_witness :
    PrimeComponentWitness 6 273 10 2 11 := by
  have hquot : primeComponentQuotient 10 6 2 = 1001 := by decide
  have hq : Nat.Prime 11 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 273)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b10_F6_A273_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 273 10 2 := by
  exact Or.inr (Or.inr ⟨11, concrete_generated_b10_F6_A273_p2_prime_witness⟩)

theorem concrete_generated_b10_F6_A273_p3_prime_witness :
    PrimeComponentWitness 6 273 10 3 37 := by
  have hquot : primeComponentQuotient 10 6 3 = 10101 := by decide
  have hq : Nat.Prime 37 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 37 ∣ 273)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b10_F6_A273_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 273 10 3 := by
  exact Or.inr (Or.inr ⟨37, concrete_generated_b10_F6_A273_p3_prime_witness⟩)

def emittedCertificate_b10_L6_A273 :
    EmittedCertificateTable 6 273 10 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b10_F6_A273_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b10_F6_A273_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b10_F6_A273_p3_prime_witness

theorem orderOf_b10_mod3663_eq_6_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 10
      (by decide : Nat.Coprime 10 3663)) = 6 := by
  let hcop : Nat.Coprime 10 3663 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 10 hcop) ∣ 6 := by
    have hpow_unit : (ZMod.unitOfCoprime 10 hcop) ^ 6 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 10 hcop : (ZMod 3663)ˣ) : ZMod 3663) ^ 6) =
        (1 : ZMod 3663)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    6 273 999999 3663 10 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 10 hcop)) 10 (by decide))
    emittedCertificate_b10_L6_A273

theorem concrete_generated_b12_F12_A203_factorization_support_cases
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

theorem concrete_generated_b12_F12_A203_p2_prime_witness :
    PrimeComponentWitness 12 203 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 203)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A203_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 203 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A203_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A203_p3_prime_witness :
    PrimeComponentWitness 12 203 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 203)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A203_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 203 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A203_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A203 :
    EmittedCertificateTable 12 203 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A203_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A203_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A203_p3_prime_witness

theorem orderOf_b12_mod43921677085_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 43921677085)) = 12 := by
  let hcop : Nat.Coprime 12 43921677085 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 43921677085)ˣ) :
          ZMod 43921677085) ^ 12) =
        (1 : ZMod 43921677085)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 203 8916100448255 43921677085 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A203

theorem concrete_generated_b12_F12_A3857_factorization_support_cases
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

theorem concrete_generated_b12_F12_A3857_p2_prime_witness :
    PrimeComponentWitness 12 3857 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 3857)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A3857_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 3857 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A3857_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A3857_p3_prime_witness :
    PrimeComponentWitness 12 3857 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 3857)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A3857_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 3857 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A3857_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A3857 :
    EmittedCertificateTable 12 3857 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A3857_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A3857_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A3857_p3_prime_witness

theorem orderOf_b12_mod2311667215_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 2311667215)) = 12 := by
  let hcop : Nat.Coprime 12 2311667215 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 2311667215)ˣ) :
          ZMod 2311667215) ^ 12) =
        (1 : ZMod 2311667215)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 3857 8916100448255 2311667215 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A3857

theorem concrete_generated_b12_F12_A5495_factorization_support_cases
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

theorem concrete_generated_b12_F12_A5495_p2_prime_witness :
    PrimeComponentWitness 12 5495 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 5495)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A5495_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5495 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A5495_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A5495_p3_prime_witness :
    PrimeComponentWitness 12 5495 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 5495)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A5495_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5495 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A5495_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A5495 :
    EmittedCertificateTable 12 5495 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A5495_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A5495_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A5495_p3_prime_witness

theorem orderOf_b12_mod1622584249_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 1622584249)) = 12 := by
  let hcop : Nat.Coprime 12 1622584249 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 1622584249)ˣ) :
          ZMod 1622584249) ^ 12) =
        (1 : ZMod 1622584249)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 5495 8916100448255 1622584249 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A5495

theorem concrete_generated_b12_F12_A60445_factorization_support_cases
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

theorem concrete_generated_b12_F12_A60445_p2_prime_witness :
    PrimeComponentWitness 12 60445 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 60445)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A60445_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 60445 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A60445_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A60445_p3_prime_witness :
    PrimeComponentWitness 12 60445 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 60445)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A60445_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 60445 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A60445_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A60445 :
    EmittedCertificateTable 12 60445 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A60445_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A60445_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A60445_p3_prime_witness

theorem orderOf_b12_mod147507659_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 147507659)) = 12 := by
  let hcop : Nat.Coprime 12 147507659 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 147507659)ˣ) :
          ZMod 147507659) ^ 12) =
        (1 : ZMod 147507659)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 60445 8916100448255 147507659 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A60445

theorem concrete_generated_b12_F12_A1752905_factorization_support_cases
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

theorem concrete_generated_b12_F12_A1752905_p2_prime_witness :
    PrimeComponentWitness 12 1752905 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 1752905)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1752905_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1752905 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A1752905_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A1752905_p3_prime_witness :
    PrimeComponentWitness 12 1752905 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 1752905)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1752905_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1752905 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A1752905_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1752905 :
    EmittedCertificateTable 12 1752905 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1752905_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1752905_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1752905_p3_prime_witness

theorem orderOf_b12_mod5086471_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 5086471)) = 12 := by
  let hcop : Nat.Coprime 12 5086471 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 5086471)ˣ) :
          ZMod 5086471) ^ 12) =
        (1 : ZMod 5086471)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1752905 8916100448255 5086471 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1752905

theorem concrete_generated_b12_F12_A391658267_factorization_support_cases
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

theorem concrete_generated_b12_F12_A391658267_p2_prime_witness :
    PrimeComponentWitness 12 391658267 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 391658267)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A391658267_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 391658267 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A391658267_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A391658267_p3_prime_witness :
    PrimeComponentWitness 12 391658267 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 391658267)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A391658267_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 391658267 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A391658267_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A391658267 :
    EmittedCertificateTable 12 391658267 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A391658267_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A391658267_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A391658267_p3_prime_witness

theorem orderOf_b12_mod22765_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 22765)) = 12 := by
  let hcop : Nat.Coprime 12 22765 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 22765)ˣ) : ZMod 22765) ^ 12) =
        (1 : ZMod 22765)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 391658267 8916100448255 22765 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A391658267

end Erdos249257
