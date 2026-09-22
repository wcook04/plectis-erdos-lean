/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos68.ChannelIntegralCongruence
import ErdosProblems.Erdos68.PaperCompleteExisting
import Solutions.PalomarCorpus.E68d.Statement

open scoped BigOperators

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E68.PaperStructuresD

/-- The local copy of `Erdos68.listLCM` is the same function. -/
theorem listLCM_transport_def : @listLCM = @Erdos68.listLCM := by
  first
  | (rfl; done)
  | (simp only [listLCM, Erdos68.listLCM]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [listLCM, Erdos68.listLCM]; done)
  | (funext a; fun_induction listLCM a <;> simp only [Erdos68.listLCM, *]; done)
  | (funext a; induction a <;> simp only [listLCM, Erdos68.listLCM, *]; done)
  | (funext a; simp [listLCM, Erdos68.listLCM]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [listLCM, Erdos68.listLCM]; done)
  | (funext a b; fun_induction listLCM a b <;> simp only [Erdos68.listLCM, *]; done)
  | (funext a b; induction b <;> simp only [listLCM, Erdos68.listLCM, *]; done)
  | (funext a b; simp [listLCM, Erdos68.listLCM]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [listLCM, Erdos68.listLCM]; done)
  | (funext a b c; fun_induction listLCM a b c <;> simp only [Erdos68.listLCM, *]; done)
  | (funext a b c; induction c <;> simp only [listLCM, Erdos68.listLCM, *]; done)
  | (funext a b c; simp [listLCM, Erdos68.listLCM]; done)
  | (simp [listLCM, Erdos68.listLCM]; done)

/-- The local copy of `Erdos68.pairwiseGCDProduct` is the same function. -/
theorem pairwiseGCDProduct_transport_def : @pairwiseGCDProduct = @Erdos68.pairwiseGCDProduct := by
  first
  | (rfl; done)
  | (simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def]; done)
  | (funext a; fun_induction pairwiseGCDProduct a <;> simp only [Erdos68.pairwiseGCDProduct, listLCM_transport_def, *]; done)
  | (funext a; induction a <;> simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def, *]; done)
  | (funext a; simp [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def]; done)
  | (funext a b; fun_induction pairwiseGCDProduct a b <;> simp only [Erdos68.pairwiseGCDProduct, listLCM_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def, *]; done)
  | (funext a b; simp [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def]; done)
  | (funext a b c; fun_induction pairwiseGCDProduct a b c <;> simp only [Erdos68.pairwiseGCDProduct, listLCM_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def, *]; done)
  | (funext a b c; simp [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def]; done)
  | (simp [pairwiseGCDProduct, Erdos68.pairwiseGCDProduct, listLCM_transport_def]; done)

theorem product_lcm_pairwise_gcd (xs : List ℕ) :
    xs.prod ∣ listLCM xs * pairwiseGCDProduct xs := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos68.PaperComplete.product_lcm_pairwise_gcd xs

end PalomarCorpus.E68.PaperStructuresD
