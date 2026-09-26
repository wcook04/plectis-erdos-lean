-- Generated direct-prime emitted certificates, part 13 of 16 (11 certificates).
import Erdos249257.CertificateKernel
import Mathlib.Tactic.NormNum.Prime
import Erdos249257.GeneratedCertificates.Part00

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F105_A31_factorization_support_cases
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
theorem concrete_generated_b2_F105_A31_p3_prime_witness :
    PrimeComponentWitness 105 31 2 3 7 := by
  have hquot : primeComponentQuotient 2 105 3 = 1180591620751771041793 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 31)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A31_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 31 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F105_A31_p3_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A31_p5_prime_witness :
    PrimeComponentWitness 105 31 2 5 71 := by
  have hquot : primeComponentQuotient 2 105 5 = 19342822337210501698682881 := by decide
  have hq : Nat.Prime 71 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 71 ∣ 31)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A31_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 31 2 5 := by
  exact Or.inr (Or.inr ⟨71, concrete_generated_b2_F105_A31_p5_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A31_p7_prime_witness :
    PrimeComponentWitness 105 31 2 7 7 := by
  have hquot : primeComponentQuotient 2 105 7 = 1237977819370199922113544193 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 31)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A31_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 31 2 7 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F105_A31_p7_prime_witness⟩)

def emittedCertificate_b2_L105_A31 :
    EmittedCertificateTable 105 31 2 where
  rows := ({3, 5, 7} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F105_A31_factorization_support_cases hp with rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A31_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A31_p5_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A31_p7_prime_witness

set_option maxRecDepth 10000 in
theorem orderOf_b2_mod1308542555074301317674016212001_eq_105_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 1308542555074301317674016212001)) = 105 := by
  let hcop : Nat.Coprime 2 1308542555074301317674016212001 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 105 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 105 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 1308542555074301317674016212001)ˣ) :
          ZMod 1308542555074301317674016212001) ^ 105) =
        (1 : ZMod 1308542555074301317674016212001)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    105 31 40564819207303340847894502572031 1308542555074301317674016212001 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L105_A31

theorem concrete_generated_b4_F12_A3_factorization_support_cases
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

theorem concrete_generated_b4_F12_A3_p2_prime_witness :
    PrimeComponentWitness 12 3 4 2 17 := by
  have hquot : primeComponentQuotient 4 12 2 = 4097 := by decide
  have hq : Nat.Prime 17 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 17 ∣ 3)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A3_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 3 4 2 := by
  exact Or.inr (Or.inr ⟨17, concrete_generated_b4_F12_A3_p2_prime_witness⟩)

theorem concrete_generated_b4_F12_A3_p3_prime_witness :
    PrimeComponentWitness 12 3 4 3 7 := by
  have hquot : primeComponentQuotient 4 12 3 = 65793 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 3)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A3_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 3 4 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b4_F12_A3_p3_prime_witness⟩)

def emittedCertificate_b4_L12_A3 :
    EmittedCertificateTable 12 3 4 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b4_F12_A3_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A3_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A3_p3_prime_witness

theorem orderOf_b4_mod5592405_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 4
      (by decide : Nat.Coprime 4 5592405)) = 12 := by
  let hcop : Nat.Coprime 4 5592405 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 4 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 4 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 4 hcop : (ZMod 5592405)ˣ) :
          ZMod 5592405) ^ 12) =
        (1 : ZMod 5592405)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 3 16777215 5592405 4 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 4 hcop)) 4 (by decide))
    emittedCertificate_b4_L12_A3

theorem concrete_lifted_b4_F12_A85_from_A17_mul5_p2_prime_witness :
    PrimeComponentWitness 12 85 4 2 241 := by
  have hquot : primeComponentQuotient 4 12 2 = 4097 := by decide
  have hq : Nat.Prime 241 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 241 ∣ 85)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b4_F12_A85_from_A17_mul5_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 85 4 2 := by
  exact Or.inr (Or.inr ⟨241, concrete_lifted_b4_F12_A85_from_A17_mul5_p2_prime_witness⟩)

theorem concrete_lifted_b4_F12_A85_from_A17_mul5_p3_prime_witness :
    PrimeComponentWitness 12 85 4 3 3 := by
  have hquot : primeComponentQuotient 4 12 3 = 65793 := by decide
  have hq : Nat.Prime 3 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 85)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b4_F12_A85_from_A17_mul5_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 85 4 3 := by
  exact Or.inr (Or.inr ⟨3, concrete_lifted_b4_F12_A85_from_A17_mul5_p3_prime_witness⟩)

theorem concrete_lifted_b6_F12_A2405_from_A481_mul5_p2_prime_witness :
    PrimeComponentWitness 12 2405 6 2 97 := by
  have hquot : primeComponentQuotient 6 12 2 = 46657 := by decide
  have hq : Nat.Prime 97 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 97 ∣ 2405)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b6_F12_A2405_from_A481_mul5_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2405 6 2 := by
  exact Or.inr (Or.inr ⟨97, concrete_lifted_b6_F12_A2405_from_A481_mul5_p2_prime_witness⟩)

theorem concrete_lifted_b6_F12_A2405_from_A481_mul5_p3_prime_witness :
    PrimeComponentWitness 12 2405 6 3 31 := by
  have hquot : primeComponentQuotient 6 12 3 = 1680913 := by decide
  have hq : Nat.Prime 31 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 31 ∣ 2405)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_lifted_b6_F12_A2405_from_A481_mul5_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2405 6 3 := by
  exact Or.inr (Or.inr ⟨31, concrete_lifted_b6_F12_A2405_from_A481_mul5_p3_prime_witness⟩)

theorem concrete_generated_b12_F12_A65_factorization_support_cases
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

theorem concrete_generated_b12_F12_A65_p2_prime_witness :
    PrimeComponentWitness 12 65 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 65)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A65_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 65 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A65_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A65_p3_prime_witness :
    PrimeComponentWitness 12 65 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 65)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A65_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 65 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A65_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A65 :
    EmittedCertificateTable 12 65 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A65_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A65_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A65_p3_prime_witness

theorem orderOf_b12_mod137170776127_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 137170776127)) = 12 := by
  let hcop : Nat.Coprime 12 137170776127 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 137170776127)ˣ) :
          ZMod 137170776127) ^ 12) =
        (1 : ZMod 137170776127)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 65 8916100448255 137170776127 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A65

theorem concrete_generated_b12_F12_A133_factorization_support_cases
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

theorem concrete_generated_b12_F12_A133_p2_prime_witness :
    PrimeComponentWitness 12 133 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 133)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A133_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 133 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A133_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A133_p3_prime_witness :
    PrimeComponentWitness 12 133 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 133)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A133_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 133 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A133_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A133 :
    EmittedCertificateTable 12 133 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A133_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A133_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A133_p3_prime_witness

theorem orderOf_b12_mod67038349235_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 67038349235)) = 12 := by
  let hcop : Nat.Coprime 12 67038349235 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 67038349235)ˣ) :
          ZMod 67038349235) ^ 12) =
        (1 : ZMod 67038349235)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 133 8916100448255 67038349235 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A133

theorem concrete_generated_b12_F12_A1885_factorization_support_cases
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

theorem concrete_generated_b12_F12_A1885_p2_prime_witness :
    PrimeComponentWitness 12 1885 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 1885)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1885_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1885 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A1885_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A1885_p3_prime_witness :
    PrimeComponentWitness 12 1885 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 1885)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1885_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1885 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A1885_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1885 :
    EmittedCertificateTable 12 1885 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1885_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1885_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1885_p3_prime_witness

theorem orderOf_b12_mod4730026763_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 4730026763)) = 12 := by
  let hcop : Nat.Coprime 12 4730026763 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 4730026763)ˣ) :
          ZMod 4730026763) ^ 12) =
        (1 : ZMod 4730026763)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1885 8916100448255 4730026763 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1885

theorem concrete_generated_b12_F12_A22765_factorization_support_cases
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

theorem concrete_generated_b12_F12_A22765_p2_prime_witness :
    PrimeComponentWitness 12 22765 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 22765)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A22765_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 22765 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A22765_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A22765_p3_prime_witness :
    PrimeComponentWitness 12 22765 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 22765)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A22765_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 22765 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A22765_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A22765 :
    EmittedCertificateTable 12 22765 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A22765_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A22765_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A22765_p3_prime_witness

theorem orderOf_b12_mod391658267_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 391658267)) = 12 := by
  let hcop : Nat.Coprime 12 391658267 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 391658267)ˣ) :
          ZMod 391658267) ^ 12) =
        (1 : ZMod 391658267)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 22765 8916100448255 391658267 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A22765

theorem concrete_generated_b12_F12_A605549_factorization_support_cases
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

theorem concrete_generated_b12_F12_A605549_p2_prime_witness :
    PrimeComponentWitness 12 605549 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 605549)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A605549_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 605549 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A605549_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A605549_p3_prime_witness :
    PrimeComponentWitness 12 605549 12 3 20593 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 605549)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A605549_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 605549 12 3 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A605549_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A605549 :
    EmittedCertificateTable 12 605549 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A605549_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A605549_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A605549_p3_prime_witness

theorem orderOf_b12_mod14723995_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 14723995)) = 12 := by
  let hcop : Nat.Coprime 12 14723995 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 14723995)ˣ) :
          ZMod 14723995) ^ 12) =
        (1 : ZMod 14723995)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 605549 8916100448255 14723995 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A605549

theorem concrete_generated_b12_F12_A30127559_factorization_support_cases
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

theorem concrete_generated_b12_F12_A30127559_p2_prime_witness :
    PrimeComponentWitness 12 30127559 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 30127559)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A30127559_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 30127559 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A30127559_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A30127559_p3_prime_witness :
    PrimeComponentWitness 12 30127559 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 30127559)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A30127559_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 30127559 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A30127559_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A30127559 :
    EmittedCertificateTable 12 30127559 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A30127559_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A30127559_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A30127559_p3_prime_witness

theorem orderOf_b12_mod295945_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 295945)) = 12 := by
  let hcop : Nat.Coprime 12 295945 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 295945)ˣ) : ZMod 295945) ^ 12) =
        (1 : ZMod 295945)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 30127559 8916100448255 295945 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A30127559

theorem concrete_generated_b12_F12_A1471060955_factorization_support_cases
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

theorem concrete_generated_b12_F12_A1471060955_p2_prime_witness :
    PrimeComponentWitness 12 1471060955 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 1471060955)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1471060955_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1471060955 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A1471060955_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A1471060955_p3_prime_witness :
    PrimeComponentWitness 12 1471060955 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 1471060955)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1471060955_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1471060955 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A1471060955_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1471060955 :
    EmittedCertificateTable 12 1471060955 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1471060955_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1471060955_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1471060955_p3_prime_witness

theorem orderOf_b12_mod6061_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 6061)) = 12 := by
  let hcop : Nat.Coprime 12 6061 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 6061)ˣ) : ZMod 6061) ^ 12) =
        (1 : ZMod 6061)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1471060955 8916100448255 6061 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1471060955

end Erdos249257
