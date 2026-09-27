-- Generated direct-prime emitted certificates, part 6 of 16 (10 certificates).
import Erdos249257.CertificateKernel
import Mathlib.Tactic.NormNum.Prime
import Erdos249257.GeneratedCertificates.Part00

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F10_A31_p2_prime_witness :
    PrimeComponentWitness 10 31 2 2 3 := by
  have hquot : primeComponentQuotient 2 10 2 = 33 := by decide
  have hq : Nat.Prime 3 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 31)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F10_A31_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 10 31 2 2 := by
  exact Or.inr (Or.inr ⟨3, concrete_generated_b2_F10_A31_p2_prime_witness⟩)

theorem concrete_generated_b2_F10_A31_p5_prime_witness :
    PrimeComponentWitness 10 31 2 5 11 := by
  have hquot : primeComponentQuotient 2 10 5 = 341 := by decide
  have hq : Nat.Prime 11 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 31)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F10_A31_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 10 31 2 5 := by
  exact Or.inr (Or.inr ⟨11, concrete_generated_b2_F10_A31_p5_prime_witness⟩)

def emittedCertificate_b2_L10_A31 :
    EmittedCertificateTable 10 31 2 where
  rows := ({2, 5} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F10_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F10_A31_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F10_A31_p5_prime_witness

theorem orderOf_b2_mod33_eq_10_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 33)) = 10 := by
  let hcop : Nat.Coprime 2 33 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 10 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 10 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 33)ˣ) : ZMod 33) ^ 10) =
        (1 : ZMod 33)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    10 31 1023 33 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L10_A31

theorem concrete_generated_b2_F105_A63119_factorization_support_cases
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
theorem concrete_generated_b2_F105_A63119_p3_prime_witness :
    PrimeComponentWitness 105 63119 2 3 7 := by
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
    have hA_factor : (63119 : Nat).factorization 7 = 1 := by
      rw [show (63119 : Nat) = 7 * 9017 by decide]
      rw [Nat.factorization_mul (by decide) (by decide)]
      simp [
        Nat.Prime.factorization_self (by decide : Nat.Prime 7),
        Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 9017),
      ]
    rw [hA_factor]
    decide

theorem concrete_generated_b2_F105_A63119_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 63119 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F105_A63119_p3_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A63119_p5_prime_witness :
    PrimeComponentWitness 105 63119 2 5 31 := by
  have hquot : primeComponentQuotient 2 105 5 = 19342822337210501698682881 := by decide
  have hq : Nat.Prime 31 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 31 ∣ 63119)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A63119_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 63119 2 5 := by
  exact Or.inr (Or.inr ⟨31, concrete_generated_b2_F105_A63119_p5_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A63119_p7_prime_witness :
    PrimeComponentWitness 105 63119 2 7 337 := by
  have hquot : primeComponentQuotient 2 105 7 = 1237977819370199922113544193 := by decide
  have hq : Nat.Prime 337 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 337 ∣ 63119)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A63119_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 63119 2 7 := by
  exact Or.inr (Or.inr ⟨337, concrete_generated_b2_F105_A63119_p7_prime_witness⟩)

def emittedCertificate_b2_L105_A63119 :
    EmittedCertificateTable 105 63119 2 where
  rows := ({3, 5, 7} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F105_A63119_factorization_support_cases hp with rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A63119_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A63119_p5_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A63119_p7_prime_witness

set_option maxRecDepth 10000 in
theorem orderOf_b2_mod642672083006754556439336849_eq_105_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 642672083006754556439336849)) = 105 := by
  let hcop : Nat.Coprime 2 642672083006754556439336849 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 105 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 105 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 642672083006754556439336849)ˣ) :
          ZMod 642672083006754556439336849) ^ 105) =
        (1 : ZMod 642672083006754556439336849)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    105 63119 40564819207303340847894502572031 642672083006754556439336849 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L105_A63119

theorem concrete_generated_b4_F6_A21_p2_prime_witness :
    PrimeComponentWitness 6 21 4 2 5 := by
  have hquot : primeComponentQuotient 4 6 2 = 65 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 21)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F6_A21_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 21 4 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b4_F6_A21_p2_prime_witness⟩)

theorem concrete_generated_b4_F6_A21_p3_prime_witness :
    PrimeComponentWitness 6 21 4 3 13 := by
  have hquot : primeComponentQuotient 4 6 3 = 273 := by decide
  have hq : Nat.Prime 13 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 13 ∣ 21)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F6_A21_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 21 4 3 := by
  exact Or.inr (Or.inr ⟨13, concrete_generated_b4_F6_A21_p3_prime_witness⟩)

def emittedCertificate_b4_L6_A21 :
    EmittedCertificateTable 6 21 4 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b4_F6_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F6_A21_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F6_A21_p3_prime_witness

theorem orderOf_b4_mod195_eq_6_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 4
      (by decide : Nat.Coprime 4 195)) = 6 := by
  let hcop : Nat.Coprime 4 195 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 4 hcop) ∣ 6 := by
    have hpow_unit : (ZMod.unitOfCoprime 4 hcop) ^ 6 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 4 hcop : (ZMod 195)ˣ) : ZMod 195) ^ 6) =
        (1 : ZMod 195)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    6 21 4095 195 4 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 4 hcop)) 4 (by decide))
    emittedCertificate_b4_L6_A21

theorem concrete_generated_b6_F12_A641173_factorization_support_cases
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

theorem concrete_generated_b6_F12_A641173_p2_prime_witness :
    PrimeComponentWitness 12 641173 6 2 97 := by
  have hquot : primeComponentQuotient 6 12 2 = 46657 := by decide
  have hq : Nat.Prime 97 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 97 ∣ 641173)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b6_F12_A641173_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 641173 6 2 := by
  exact Or.inr (Or.inr ⟨97, concrete_generated_b6_F12_A641173_p2_prime_witness⟩)

theorem concrete_generated_b6_F12_A641173_p3_prime_witness :
    PrimeComponentWitness 12 641173 6 3 97 := by
  have hquot : primeComponentQuotient 6 12 3 = 1680913 := by decide
  have hq : Nat.Prime 97 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 97 ∣ 641173)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b6_F12_A641173_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 641173 6 3 := by
  exact Or.inr (Or.inr ⟨97, concrete_generated_b6_F12_A641173_p3_prime_witness⟩)

def emittedCertificate_b6_L12_A641173 :
    EmittedCertificateTable 12 641173 6 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b6_F12_A641173_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b6_F12_A641173_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b6_F12_A641173_p3_prime_witness

theorem orderOf_b6_mod3395_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 6
      (by decide : Nat.Coprime 6 3395)) = 12 := by
  let hcop : Nat.Coprime 6 3395 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 6 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 6 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 6 hcop : (ZMod 3395)ˣ) : ZMod 3395) ^ 12) =
        (1 : ZMod 3395)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 641173 2176782335 3395 6 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 6 hcop)) 6 (by decide))
    emittedCertificate_b6_L12_A641173

theorem concrete_generated_b12_F12_A5_factorization_support_cases
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

theorem concrete_generated_b12_F12_A5_p2_prime_witness :
    PrimeComponentWitness 12 5 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 5)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A5_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A5_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A5_p3_prime_witness :
    PrimeComponentWitness 12 5 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 5)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A5_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A5_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A5 :
    EmittedCertificateTable 12 5 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A5_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A5_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A5_p3_prime_witness

theorem orderOf_b12_mod1783220089651_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 1783220089651)) = 12 := by
  let hcop : Nat.Coprime 12 1783220089651 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 1783220089651)ˣ) :
          ZMod 1783220089651) ^ 12) =
        (1 : ZMod 1783220089651)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 5 8916100448255 1783220089651 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A5

theorem concrete_generated_b12_F12_A1015_factorization_support_cases
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

theorem concrete_generated_b12_F12_A1015_p2_prime_witness :
    PrimeComponentWitness 12 1015 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 1015)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1015_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1015 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A1015_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A1015_p3_prime_witness :
    PrimeComponentWitness 12 1015 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 1015)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1015_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1015 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A1015_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1015 :
    EmittedCertificateTable 12 1015 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1015_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1015_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1015_p3_prime_witness

theorem orderOf_b12_mod8784335417_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 8784335417)) = 12 := by
  let hcop : Nat.Coprime 12 8784335417 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 8784335417)ˣ) :
          ZMod 8784335417) ^ 12) =
        (1 : ZMod 8784335417)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1015 8916100448255 8784335417 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1015

theorem concrete_generated_b12_F12_A13585_factorization_support_cases
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

theorem concrete_generated_b12_F12_A13585_p2_prime_witness :
    PrimeComponentWitness 12 13585 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 13585)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A13585_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 13585 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A13585_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A13585_p3_prime_witness :
    PrimeComponentWitness 12 13585 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 13585)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A13585_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 13585 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A13585_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A13585 :
    EmittedCertificateTable 12 13585 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A13585_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A13585_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A13585_p3_prime_witness

theorem orderOf_b12_mod656319503_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 656319503)) = 12 := by
  let hcop : Nat.Coprime 12 656319503 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 656319503)ˣ) :
          ZMod 656319503) ^ 12) =
        (1 : ZMod 656319503)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 13585 8916100448255 656319503 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A13585

theorem concrete_generated_b12_F12_A50141_factorization_support_cases
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

theorem concrete_generated_b12_F12_A50141_p2_prime_witness :
    PrimeComponentWitness 12 50141 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 50141)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A50141_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 50141 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A50141_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A50141_p3_prime_witness :
    PrimeComponentWitness 12 50141 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 50141)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A50141_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 50141 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A50141_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A50141 :
    EmittedCertificateTable 12 50141 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A50141_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A50141_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A50141_p3_prime_witness

theorem orderOf_b12_mod177820555_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 177820555)) = 12 := by
  let hcop : Nat.Coprime 12 177820555 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 177820555)ˣ) :
          ZMod 177820555) ^ 12) =
        (1 : ZMod 177820555)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 50141 8916100448255 177820555 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A50141

theorem concrete_generated_b12_F12_A250415_factorization_support_cases
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

theorem concrete_generated_b12_F12_A250415_p2_prime_witness :
    PrimeComponentWitness 12 250415 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 250415)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A250415_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 250415 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A250415_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A250415_p3_prime_witness :
    PrimeComponentWitness 12 250415 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 250415)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A250415_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 250415 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A250415_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A250415 :
    EmittedCertificateTable 12 250415 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A250415_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A250415_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A250415_p3_prime_witness

theorem orderOf_b12_mod35605297_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 35605297)) = 12 := by
  let hcop : Nat.Coprime 12 35605297 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 35605297)ˣ) :
          ZMod 35605297) ^ 12) =
        (1 : ZMod 35605297)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 250415 8916100448255 35605297 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A250415

theorem concrete_generated_b12_F12_A5622955_factorization_support_cases
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

theorem concrete_generated_b12_F12_A5622955_p2_prime_witness :
    PrimeComponentWitness 12 5622955 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 5622955)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A5622955_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5622955 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A5622955_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A5622955_p3_prime_witness :
    PrimeComponentWitness 12 5622955 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 5622955)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A5622955_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 5622955 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A5622955_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A5622955 :
    EmittedCertificateTable 12 5622955 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A5622955_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A5622955_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A5622955_p3_prime_witness

theorem orderOf_b12_mod1585661_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 1585661)) = 12 := by
  let hcop : Nat.Coprime 12 1585661 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 1585661)ˣ) :
          ZMod 1585661) ^ 12) =
        (1 : ZMod 1585661)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 5622955 8916100448255 1585661 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A5622955

end Erdos249257
