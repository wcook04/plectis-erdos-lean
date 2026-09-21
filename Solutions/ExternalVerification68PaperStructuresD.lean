/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/
import ErdosProblems.Erdos68.ChannelIntegralCongruence
import ErdosProblems.Erdos68.PaperCompleteExisting

/-!
# Independent restatements for Erdős problem #68

Each theorem below restates a refereed declaration of the substantive development in
this repository, at public commit `f436a7ec0f7bf035828a7eec37fd29ae74d17d84` of
https://github.com/wcook04/plectis-erdos. The definitions are local copies of the source definitions, so
the statements elaborate against Mathlib alone. This module is a comparison interface
over that development, not the development itself. The mathematics is developed in
`ErdosProblems.Erdos68.ChannelIntegralCongruence`,
`ErdosProblems.Erdos68.PaperCompleteExisting`.
-/

open scoped BigOperators

namespace Erdos249257.ExternalVerification68PaperStructuresD

noncomputable def listLCM : List ℕ → ℕ
  | [] => 1
  | a :: tail => Nat.lcm a (listLCM tail)

noncomputable def pairwiseGCDProduct : List ℕ → ℕ
  | [] => 1
  | a :: tail =>
      (tail.map (Nat.gcd a)).prod * pairwiseGCDProduct tail

/-! ### Transport bridges

A copied structure is a separate type from its source, and a copied recursive
definition is a separate compilation of the same recursion, so a statement that
mentions one is not proved by direct application. The bridges below are what the
transports use; they are generated, elaborated here, and recorded as derived
transport in the entry metadata.
-/

/-- The local copy of `Erdos68.listLCM` is the same function: a separate compilation of
the same recursion, which a direct application does not always see through. -/
theorem listLCM_transport_def : @listLCM = @Erdos68.listLCM := by
  first
  | rfl
  | (funext x; induction x <;> simp only [listLCM, Erdos68.listLCM, *])
  | (funext x; simp only [listLCM, Erdos68.listLCM])
  | (funext x y; induction x <;> simp only [listLCM, Erdos68.listLCM, *])

/-- The local copy of `Erdos68.pairwiseGCDProduct` is the same function: a separate compilation of
the same recursion, which a direct application does not always see through. -/
theorem pairwiseGCDProduct_transport_def : @pairwiseGCDProduct = @Erdos68.pairwiseGCDProduct := by
  first
  | rfl
  | (funext x; induction x <;> simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, *])
  | (funext x; simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct])
  | (funext x y; induction x <;> simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, *])

theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ listLCM xs * pairwiseGCDProduct xs := by
  simp only [listLCM_transport_def, pairwiseGCDProduct_transport_def]
  exact @ErdosProblems.Erdos68.PaperComplete.product_lcm_pairwise_gcd xs

end Erdos249257.ExternalVerification68PaperStructuresD
