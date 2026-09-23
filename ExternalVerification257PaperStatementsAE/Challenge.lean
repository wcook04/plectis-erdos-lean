/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import Mathlib

set_option autoImplicit false

/-!
# Independent restatements for Erdős problem #257

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`Erdos249257.GenericTailOrbitRigidity`.
-/

open Filter
open Set

namespace Erdos249257.ExternalVerification257PaperStatementsAE

noncomputable def HasRationalValue (x : ℝ) : Prop :=
  ∃ p : ℤ, ∃ v : ℕ, 0 < v ∧ x = (p : ℝ) / (v : ℝ)

noncomputable def IsTemperedBinaryOrbit (c : ℕ → ℕ) (v : ℕ) (u : ℕ → ℤ) : Prop :=
  (∀ N : ℕ,
      u (N + 1) = 2 * u N - ((v * c (N + 1) : ℕ) : ℤ)) ∧
    Tendsto (fun N : ℕ ↦ (u N : ℝ) / (2 : ℝ) ^ N) atTop (nhds 0)

noncomputable def balancedPulseRadius (m : ℕ) : ℕ := (m + 1) / 2

noncomputable def balancedPulseCoeff (m r : ℕ) : ℕ → ℕ := fun n ↦
  if n = m then balancedPulseRadius m - r
  else if n = m + 1 then 2 * r
  else 0

noncomputable def binaryCoeffSeries (c : ℕ → ℕ) : ℝ :=
  ∑' n : ℕ, (c (n + 1) : ℝ) / (2 : ℝ) ^ (n + 1)

noncomputable def binaryCoeffTail (c : ℕ → ℕ) (N : ℕ) : ℝ :=
  ∑' j : ℕ, (c (N + j + 1) : ℝ) / (2 : ℝ) ^ (j + 1)

/-- States prop:local-void from the long record for Erdős problem #257. Transported from
Erdos249257.balancedPulse_endpoint_fanout in the substantive development, whose statement
was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_endpoint_fanout (m r : ℕ) :
    balancedPulseCoeff m r (m + 1) / 2 = r := by
  sorry

/-- States prop:local-void from the long record for Erdős problem #257. Transported from
Erdos249257.balancedPulse_label_card_lower_bound in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_label_card_lower_bound
    {m : ℕ} {Λ : Type*} [Fintype Λ]
    (label : Fin (balancedPulseRadius m + 1) → Λ)
    (decode : Λ → ℕ) (hdecode : ∀ r, decode (label r) = r) :
    balancedPulseRadius m + 1 ≤ Fintype.card Λ := by
  sorry

/-- States prop:local-void from the long record for Erdős problem #257. Transported from
Erdos249257.balancedPulse_no_autonomous_decoder in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_no_autonomous_decoder
    {State : Type*} (m : ℕ) (hm : 2 ≤ m)
    (state : Fin (balancedPulseRadius m + 1) → State)
    (hstate : ∀ r, state r = state ⟨0, by simp⟩) :
    ¬ ∃ decode : State → ℕ, ∀ r, decode (state r) = r := by
  sorry

/-- States prop:finite-state-nogo, prop:local-void from the long record for Erdős problem #257.
Transported from Erdos249257.balancedPulse_weighted_pair in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem balancedPulse_weighted_pair
    {m r : ℕ} (hr : r ≤ balancedPulseRadius m) :
    2 * balancedPulseCoeff m r m + balancedPulseCoeff m r (m + 1) =
      2 * balancedPulseRadius m := by
  sorry

/-- States thm:tempered-orbit-rigidity from the long record for Erdős problem #257. Transported
from Erdos249257.binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem binaryCoeffSeries_rational_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    HasRationalValue (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := by
  sorry

/-- States record:257bm-i2 from the long record for Erdős problem #257. Transported from
Erdos249257.binaryCoeffTail_div_pow_tendsto_zero in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem binaryCoeffTail_div_pow_tendsto_zero
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    Tendsto (fun N : ℕ ↦ binaryCoeffTail c N / (2 : ℝ) ^ N) atTop (nhds 0) := by
  sorry

/-- States record:257bm-i2 from the long record for Erdős problem #257. Transported from
Erdos249257.binaryCoeffTail_le in the substantive development, whose statement was refereed
against the paper in the coverage ledger. -/
theorem binaryCoeffTail_le (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) (N : ℕ) :
    binaryCoeffTail c N ≤ (N : ℝ) + 2 := by
  sorry

/-- States lem:collapse-mech, thm:middle-allright-defect from the long record for Erdős problem
#257. Transported from Erdos249257.binaryCoeffTail_nonneg in the substantive development,
whose statement was refereed against the paper in the coverage ledger. -/
theorem binaryCoeffTail_nonneg (c : ℕ → ℕ) (N : ℕ) :
    0 ≤ binaryCoeffTail c N := by
  sorry

/-- States record:257bm-i-t7 from the long record for Erdős problem #257. Transported from
Erdos249257.not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit in the
substantive development, whose statement was refereed against the paper in the coverage
ledger. -/
theorem not_irrational_binaryCoeffSeries_iff_exists_temperedBinaryOrbit
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n) :
    ¬ Irrational (binaryCoeffSeries c) ↔
      ∃ v : ℕ, 0 < v ∧ ∃ u : ℕ → ℤ, IsTemperedBinaryOrbit c v u := by
  sorry

/-- States thm:tempered-orbit-rigidity from the long record for Erdős problem #257. Transported
from Erdos249257.temperedBinaryOrbit_eq_scaledTail in the substantive development, whose
statement was refereed against the paper in the coverage ledger. -/
theorem temperedBinaryOrbit_eq_scaledTail
    (c : ℕ → ℕ) (hgrowth : ∀ n : ℕ, c n ≤ n)
    {v : ℕ} {u : ℕ → ℤ} (horbit : IsTemperedBinaryOrbit c v u) :
    ∀ N : ℕ, (u N : ℝ) = (v : ℝ) * binaryCoeffTail c N := by
  sorry

end Erdos249257.ExternalVerification257PaperStatementsAE
