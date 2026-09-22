/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import Erdos249257.TotientMahlerDefect
import Solutions.PalomarCorpus.E249p.Statement

open Module
open Matrix

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E249.PaperStructuresP

/-- The copied structure `SeparatedMinorCertificate` and its source `Erdos249257.SeparatedMinorCertificate` carry the same
fields, so each converts into the other field by field. -/
noncomputable def SeparatedMinorCertificate_transport_toSrc {ι : Type*} [Fintype ι] [DecidableEq ι] {family : ι → ℕ → ℚ} (x : @SeparatedMinorCertificate ι inferInstance inferInstance family) :
    @Erdos249257.SeparatedMinorCertificate ι inferInstance inferInstance family :=
  ⟨x.rowIndex, x.det_ne_zero⟩

/-- The inverse of `SeparatedMinorCertificate_transport_toSrc`. -/
noncomputable def SeparatedMinorCertificate_transport_ofSrc {ι : Type*} [Fintype ι] [DecidableEq ι] {family : ι → ℕ → ℚ} (x : @Erdos249257.SeparatedMinorCertificate ι inferInstance inferInstance family) :
    @SeparatedMinorCertificate ι inferInstance inferInstance family :=
  ⟨x.rowIndex, x.det_ne_zero⟩

@[simp] theorem SeparatedMinorCertificate_transport_toSrc_rowIndex {ι : Type*} [Fintype ι] [DecidableEq ι] {family : ι → ℕ → ℚ}
    (x : @SeparatedMinorCertificate ι inferInstance inferInstance family) :
    (SeparatedMinorCertificate_transport_toSrc x).rowIndex = x.rowIndex := rfl

@[simp] theorem SeparatedMinorCertificate_transport_ofSrc_rowIndex {ι : Type*} [Fintype ι] [DecidableEq ι] {family : ι → ℕ → ℚ}
    (x : @Erdos249257.SeparatedMinorCertificate ι inferInstance inferInstance family) :
    (SeparatedMinorCertificate_transport_ofSrc x).rowIndex = x.rowIndex := rfl

theorem linearIndependent_of_separatedMinorCertificate
    {ι : Type*} [Fintype ι] [DecidableEq ι] (family : ι → ℕ → ℚ)
    (cert : SeparatedMinorCertificate family) :
    LinearIndependent ℚ family := @Erdos249257.linearIndependent_of_separatedMinorCertificate ι inferInstance inferInstance family (SeparatedMinorCertificate_transport_toSrc cert)

end PalomarCorpus.E249.PaperStructuresP
