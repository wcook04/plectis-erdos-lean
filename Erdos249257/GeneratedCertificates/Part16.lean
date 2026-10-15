-- Generated direct-prime emitted certificates, part 16 of 16 (10 certificates).
import Erdos249257.CertificateKernel
import Mathlib.Tactic.NormNum.Prime
import Erdos249257.GeneratedCertificates.Part00

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

namespace Erdos249257

theorem concrete_generated_b2_F105_A332351_factorization_support_cases
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
theorem concrete_generated_b2_F105_A332351_p3_prime_witness :
    PrimeComponentWitness 105 332351 2 3 7 := by
  have hquot : primeComponentQuotient 2 105 3 = 1180591620751771041793 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 332351)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A332351_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 332351 2 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F105_A332351_p3_prime_witness⟩)

theorem concrete_generated_b2_F105_A332351_p5_prime_witness :
    PrimeComponentWitness 105 332351 2 5 29191 := by
  have hquot : primeComponentQuotient 2 105 5 = 19342822337210501698682881 := by decide
  have hq : Nat.Prime 29191 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29191 ∣ 332351)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A332351_p5_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 332351 2 5 := by
  exact Or.inr (Or.inr ⟨29191, concrete_generated_b2_F105_A332351_p5_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b2_F105_A332351_p7_prime_witness :
    PrimeComponentWitness 105 332351 2 7 7 := by
  have hquot : primeComponentQuotient 2 105 7 = 1237977819370199922113544193 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 332351)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b2_F105_A332351_p7_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 105 332351 2 7 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b2_F105_A332351_p7_prime_witness⟩)

def emittedCertificate_b2_L105_A332351 :
    EmittedCertificateTable 105 332351 2 where
  rows := ({3, 5, 7} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b2_F105_A332351_factorization_support_cases hp with rfl | rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A332351_p3_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A332351_p5_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b2_F105_A332351_p7_prime_witness

set_option maxRecDepth 10000 in
theorem orderOf_b2_mod122054151205512668377391681_eq_105_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 2
      (by decide : Nat.Coprime 2 122054151205512668377391681)) = 105 := by
  let hcop : Nat.Coprime 2 122054151205512668377391681 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 2 hcop) ∣ 105 := by
    have hpow_unit : (ZMod.unitOfCoprime 2 hcop) ^ 105 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 2 hcop : (ZMod 122054151205512668377391681)ˣ) :
          ZMod 122054151205512668377391681) ^ 105) =
        (1 : ZMod 122054151205512668377391681)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    105 332351 40564819207303340847894502572031 122054151205512668377391681 2 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 2 hcop)) 2 (by decide))
    emittedCertificate_b2_L105_A332351

theorem concrete_generated_b4_F12_A4641_factorization_support_cases
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

set_option maxRecDepth 10000 in
theorem concrete_generated_b4_F12_A4641_p2_prime_witness :
    PrimeComponentWitness 12 4641 4 2 241 := by
  have hquot : primeComponentQuotient 4 12 2 = 4097 := by decide
  have hq : Nat.Prime 241 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 241 ∣ 4641)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A4641_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 4641 4 2 := by
  exact Or.inr (Or.inr ⟨241, concrete_generated_b4_F12_A4641_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b4_F12_A4641_p3_prime_witness :
    PrimeComponentWitness 12 4641 4 3 241 := by
  have hquot : primeComponentQuotient 4 12 3 = 65793 := by decide
  have hq : Nat.Prime 241 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 241 ∣ 4641)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b4_F12_A4641_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 4641 4 3 := by
  exact Or.inr (Or.inr ⟨241, concrete_generated_b4_F12_A4641_p3_prime_witness⟩)

def emittedCertificate_b4_L12_A4641 :
    EmittedCertificateTable 12 4641 4 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b4_F12_A4641_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A4641_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b4_F12_A4641_p3_prime_witness

theorem orderOf_b4_mod3615_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 4
      (by decide : Nat.Coprime 4 3615)) = 12 := by
  let hcop : Nat.Coprime 4 3615 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 4 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 4 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 4 hcop : (ZMod 3615)ˣ) : ZMod 3615) ^ 12) =
        (1 : ZMod 3615)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 4641 16777215 3615 4 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 4 hcop)) 4 (by decide))
    emittedCertificate_b4_L12_A4641

theorem concrete_generated_b6_F6_A31_p2_prime_witness :
    PrimeComponentWitness 6 31 6 2 7 := by
  have hquot : primeComponentQuotient 6 6 2 = 217 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 31)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b6_F6_A31_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 31 6 2 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b6_F6_A31_p2_prime_witness⟩)

theorem concrete_generated_b6_F6_A31_p3_prime_witness :
    PrimeComponentWitness 6 31 6 3 43 := by
  have hquot : primeComponentQuotient 6 6 3 = 1333 := by decide
  have hq : Nat.Prime 43 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 43 ∣ 31)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b6_F6_A31_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 31 6 3 := by
  exact Or.inr (Or.inr ⟨43, concrete_generated_b6_F6_A31_p3_prime_witness⟩)

def emittedCertificate_b6_L6_A31 :
    EmittedCertificateTable 6 31 6 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b6_F6_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b6_F6_A31_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b6_F6_A31_p3_prime_witness

theorem orderOf_b6_mod1505_eq_6_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 6
      (by decide : Nat.Coprime 6 1505)) = 6 := by
  let hcop : Nat.Coprime 6 1505 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 6 hcop) ∣ 6 := by
    have hpow_unit : (ZMod.unitOfCoprime 6 hcop) ^ 6 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 6 hcop : (ZMod 1505)ˣ) : ZMod 1505) ^ 6) =
        (1 : ZMod 1505)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    6 31 46655 1505 6 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 6 hcop)) 6 (by decide))
    emittedCertificate_b6_L6_A31

theorem concrete_generated_b10_F6_A7_factorization_support_cases
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

theorem concrete_generated_b10_F6_A7_p2_prime_witness :
    PrimeComponentWitness 6 7 10 2 11 := by
  have hquot : primeComponentQuotient 10 6 2 = 1001 := by decide
  have hq : Nat.Prime 11 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 11 ∣ 7)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b10_F6_A7_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 7 10 2 := by
  exact Or.inr (Or.inr ⟨11, concrete_generated_b10_F6_A7_p2_prime_witness⟩)

theorem concrete_generated_b10_F6_A7_p3_prime_witness :
    PrimeComponentWitness 6 7 10 3 3 := by
  have hquot : primeComponentQuotient 10 6 3 = 10101 := by decide
  have hq : Nat.Prime 3 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 3 ∣ 7)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b10_F6_A7_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 6 7 10 3 := by
  exact Or.inr (Or.inr ⟨3, concrete_generated_b10_F6_A7_p3_prime_witness⟩)

def emittedCertificate_b10_L6_A7 :
    EmittedCertificateTable 6 7 10 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b10_F6_A7_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b10_F6_A7_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b10_F6_A7_p3_prime_witness

theorem orderOf_b10_mod142857_eq_6_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 10
      (by decide : Nat.Coprime 10 142857)) = 6 := by
  let hcop : Nat.Coprime 10 142857 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 10 hcop) ∣ 6 := by
    have hpow_unit : (ZMod.unitOfCoprime 10 hcop) ^ 6 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 10 hcop : (ZMod 142857)ˣ) : ZMod 142857) ^ 6) =
        (1 : ZMod 142857)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    6 7 999999 142857 10 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 10 hcop)) 10 (by decide))
    emittedCertificate_b10_L6_A7

theorem concrete_generated_b12_F12_A95_factorization_support_cases
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

theorem concrete_generated_b12_F12_A95_p2_prime_witness :
    PrimeComponentWitness 12 95 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 95)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A95_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 95 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A95_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A95_p3_prime_witness :
    PrimeComponentWitness 12 95 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 95)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A95_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 95 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A95_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A95 :
    EmittedCertificateTable 12 95 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A95_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A95_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A95_p3_prime_witness

theorem orderOf_b12_mod93853688929_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 93853688929)) = 12 := by
  let hcop : Nat.Coprime 12 93853688929 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 93853688929)ˣ) :
          ZMod 93853688929) ^ 12) =
        (1 : ZMod 93853688929)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 95 8916100448255 93853688929 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A95

theorem concrete_generated_b12_F12_A2755_factorization_support_cases
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

theorem concrete_generated_b12_F12_A2755_p2_prime_witness :
    PrimeComponentWitness 12 2755 12 2 20593 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 2755)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A2755_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2755 12 2 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A2755_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A2755_p3_prime_witness :
    PrimeComponentWitness 12 2755 12 3 7 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 7 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 7 ∣ 2755)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A2755_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2755 12 3 := by
  exact Or.inr (Or.inr ⟨7, concrete_generated_b12_F12_A2755_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A2755 :
    EmittedCertificateTable 12 2755 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A2755_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A2755_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A2755_p3_prime_witness

theorem orderOf_b12_mod3236334101_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 3236334101)) = 12 := by
  let hcop : Nat.Coprime 12 3236334101 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 3236334101)ˣ) :
          ZMod 3236334101) ^ 12) =
        (1 : ZMod 3236334101)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 2755 8916100448255 3236334101 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A2755

theorem concrete_generated_b12_F12_A31871_factorization_support_cases
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

theorem concrete_generated_b12_F12_A31871_p2_prime_witness :
    PrimeComponentWitness 12 31871 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 31871)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A31871_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 31871 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A31871_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A31871_p3_prime_witness :
    PrimeComponentWitness 12 31871 12 3 19 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 19 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 19 ∣ 31871)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A31871_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 31871 12 3 := by
  exact Or.inr (Or.inr ⟨19, concrete_generated_b12_F12_A31871_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A31871 :
    EmittedCertificateTable 12 31871 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A31871_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A31871_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A31871_p3_prime_witness

theorem orderOf_b12_mod279755905_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 279755905)) = 12 := by
  let hcop : Nat.Coprime 12 279755905 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 279755905)ˣ) :
          ZMod 279755905) ^ 12) =
        (1 : ZMod 279755905)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 31871 8916100448255 279755905 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A31871

theorem concrete_generated_b12_F12_A1148455_factorization_support_cases
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

theorem concrete_generated_b12_F12_A1148455_p2_prime_witness :
    PrimeComponentWitness 12 1148455 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 1148455)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1148455_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1148455 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A1148455_p2_prime_witness⟩)

theorem concrete_generated_b12_F12_A1148455_p3_prime_witness :
    PrimeComponentWitness 12 1148455 12 3 20593 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 20593 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 20593 ∣ 1148455)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A1148455_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 1148455 12 3 := by
  exact Or.inr (Or.inr ⟨20593, concrete_generated_b12_F12_A1148455_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A1148455 :
    EmittedCertificateTable 12 1148455 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A1148455_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1148455_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A1148455_p3_prime_witness

theorem orderOf_b12_mod7763561_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 7763561)) = 12 := by
  let hcop : Nat.Coprime 12 7763561 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 7763561)ˣ) :
          ZMod 7763561) ^ 12) =
        (1 : ZMod 7763561)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 1148455 8916100448255 7763561 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A1148455

theorem concrete_generated_b12_F12_A2738869_factorization_support_cases
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

theorem concrete_generated_b12_F12_A2738869_p2_prime_witness :
    PrimeComponentWitness 12 2738869 12 2 5 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 5 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 5 ∣ 2738869)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A2738869_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2738869 12 2 := by
  exact Or.inr (Or.inr ⟨5, concrete_generated_b12_F12_A2738869_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A2738869_p3_prime_witness :
    PrimeComponentWitness 12 2738869 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 2738869)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A2738869_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 2738869 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A2738869_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A2738869 :
    EmittedCertificateTable 12 2738869 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A2738869_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A2738869_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A2738869_p3_prime_witness

theorem orderOf_b12_mod3255395_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 3255395)) = 12 := by
  let hcop : Nat.Coprime 12 3255395 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 3255395)ˣ) :
          ZMod 3255395) ^ 12) =
        (1 : ZMod 3255395)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 2738869 8916100448255 3255395 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A2738869

theorem concrete_generated_b12_F12_A150637795_factorization_support_cases
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

theorem concrete_generated_b12_F12_A150637795_p2_prime_witness :
    PrimeComponentWitness 12 150637795 12 2 29 := by
  have hquot : primeComponentQuotient 12 12 2 = 2985985 := by decide
  have hq : Nat.Prime 29 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 29 ∣ 150637795)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A150637795_p2_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 150637795 12 2 := by
  exact Or.inr (Or.inr ⟨29, concrete_generated_b12_F12_A150637795_p2_prime_witness⟩)

set_option maxRecDepth 10000 in
theorem concrete_generated_b12_F12_A150637795_p3_prime_witness :
    PrimeComponentWitness 12 150637795 12 3 157 := by
  have hquot : primeComponentQuotient 12 12 3 = 430002433 := by decide
  have hq : Nat.Prime 157 := by norm_num
  refine ⟨hq, ?_, ?_⟩
  · rw [hquot]
    decide
  · rw [hquot, Nat.factorization_eq_zero_of_not_dvd (by decide : ¬ 157 ∣ 150637795)]
    exact hq.factorization_pos_of_dvd (by decide) (by decide)

theorem concrete_generated_b12_F12_A150637795_p3_CanonicalWitnessRowCase :
    CanonicalWitnessRowCase 12 150637795 12 3 := by
  exact Or.inr (Or.inr ⟨157, concrete_generated_b12_F12_A150637795_p3_prime_witness⟩)

def emittedCertificate_b12_L12_A150637795 :
    EmittedCertificateTable 12 150637795 12 where
  rows := ({2, 3} : Finset Nat)
  L_ne_zero := by decide
  covers_factor_support := by
    intro p hp
    rcases concrete_generated_b12_F12_A150637795_factorization_support_cases hp with rfl | rfl <;>
      simp
  row_sound := by
    intro p hp
    simp at hp
    rcases hp with hp_eq | hp_eq
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A150637795_p2_prime_witness
    · subst p
      exact EmittedGeneratedRowCase.prime_witness
        concrete_generated_b12_F12_A150637795_p3_prime_witness

theorem orderOf_b12_mod59189_eq_12_from_emittedCertificate_denNorm :
    orderOf (ZMod.unitOfCoprime 12
      (by decide : Nat.Coprime 12 59189)) = 12 := by
  let hcop : Nat.Coprime 12 59189 := by decide
  have h_ord_dvd_L : orderOf (ZMod.unitOfCoprime 12 hcop) ∣ 12 := by
    have hpow_unit : (ZMod.unitOfCoprime 12 hcop) ^ 12 = 1 := by
      apply Units.ext
      change (((ZMod.unitOfCoprime 12 hcop : (ZMod 59189)ˣ) : ZMod 59189) ^ 12) =
        (1 : ZMod 59189)
      rw [ZMod.coe_unitOfCoprime, ← Nat.cast_pow, ← Nat.cast_one,
        ZMod.natCast_eq_natCast_iff']
      decide
    exact (orderOf_dvd_iff_pow_eq_one).2 hpow_unit
  exact finite_period_noncollapse_from_emitted_certificate_table
    12 150637795 8916100448255 59189 12 hcop
    (by decide)
    (by decide)
    h_ord_dvd_L
    (by decide)
    (by decide)
    (by decide)
    (Nat.one_le_pow (orderOf (ZMod.unitOfCoprime 12 hcop)) 12 (by decide))
    emittedCertificate_b12_L12_A150637795

end Erdos249257
