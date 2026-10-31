/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperCompleteR21.SourceCoefficientHeights
import ErdosProblems.Erdos1049.PaperLongCapR9
import ErdosProblems.Erdos1049.PaperOmegaIndicatorR7
import ErdosProblems.Erdos1049.QBinomialUnitIdentity
import ErdosProblems.Erdos1049.SourceBClearingR12
import ErdosProblems.Erdos1049.SourceBMonomialR12
import ErdosProblems.Erdos1049.SourceBTopDegreeR13
import ErdosProblems.Erdos1049.SourcePolynomialR11
import Solutions.PalomarCorpus.E1049_02.Statement

open Filter
open Polynomial
open scoped BigOperators
open Finset
open Asymptotics
open scoped Topology

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStructuresQ
export PalomarCorpus.E1049_02.Shared (maxCoeffNat maxPairHeight)

theorem gaussBinom_transport_def : @gaussBinom = @ErdosProblems.Erdos1049.gaussBinom := by
  first
  | (rfl; done)
  | (simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom]; done)
  | (with_unfolding_all rfl; done)
  | (unfold gaussBinom ErdosProblems.Erdos1049.gaussBinom; done)
  | (unfold gaussBinom ErdosProblems.Erdos1049.gaussBinom <;> simp only [ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (ext x; simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom]; done)
  | (funext a; fun_induction gaussBinom a <;> simp only [ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a; induction a <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a; induction a <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a; induction a <;> simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a; simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom]; done)
  | (funext a b; fun_induction gaussBinom a b <;> simp only [ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b; induction b <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b; induction a generalizing b <;> simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b; induction b generalizing a <;> simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b; simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom]; done)
  | (funext a b c; fun_induction gaussBinom a b c <;> simp only [ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b c; induction c <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext a b c; simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom]; done)
  | (simp [gaussBinom, ErdosProblems.Erdos1049.gaussBinom]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom] <;> rfl; done)
  | (funext v1 v2; simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom] <;> rfl; done)
  | (funext v1 v2 v3; simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom] <;> rfl; done)
  | (funext v1 v2 v3 v4; simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom] <;> rfl; done)
  | (funext v1 v2 v3 v4; fun_induction gaussBinom v1 v2 v3 v4 <;> simp only [ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4; induction v1 generalizing v2 v3 v4 <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4; induction v2 generalizing v1 v3 v4 <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4; induction v3 generalizing v1 v2 v4 <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4; induction v4 generalizing v1 v2 v3 <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4 v5; simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom] <;> rfl; done)
  | (funext v1 v2 v3 v4 v5; fun_induction gaussBinom v1 v2 v3 v4 v5 <;> simp only [ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4 v5; induction v1 generalizing v2 v3 v4 v5 <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4 v5; induction v2 generalizing v1 v3 v4 v5 <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4 v5; induction v3 generalizing v1 v2 v4 v5 <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4 v5; induction v4 generalizing v1 v2 v3 v5 <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)
  | (funext v1 v2 v3 v4 v5; induction v5 generalizing v1 v2 v3 v4 <;> simp only [gaussBinom, ErdosProblems.Erdos1049.gaussBinom, *]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct` is the same function. -/
theorem sourceGaussianProduct_transport_def : @sourceGaussianProduct = @ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct := by
  first
  | (rfl; done)
  | (simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold sourceGaussianProduct ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct; done)
  | (unfold sourceGaussianProduct ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (ext x; simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def]; done)
  | (funext a; fun_induction sourceGaussianProduct a <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a; induction a <;> simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a; simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def]; done)
  | (funext a b; fun_induction sourceGaussianProduct a b <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b; simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def]; done)
  | (funext a b c; fun_induction sourceGaussianProduct a b c <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def, *]; done)
  | (funext a b c; simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def]; done)
  | (simp [sourceGaussianProduct, ErdosProblems.Erdos1049.PaperR11.sourceGaussianProduct, gaussBinom_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperR11.sourceASummand` is the same function. -/
theorem sourceASummand_transport_def : @sourceASummand = @ErdosProblems.Erdos1049.PaperR11.sourceASummand := by
  first
  | (rfl; done)
  | (simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold sourceASummand ErdosProblems.Erdos1049.PaperR11.sourceASummand; done)
  | (unfold sourceASummand ErdosProblems.Erdos1049.PaperR11.sourceASummand <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (ext x; simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def]; done)
  | (funext a; fun_induction sourceASummand a <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a; induction a <;> simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a; simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def]; done)
  | (funext a b; fun_induction sourceASummand a b <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b; simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def]; done)
  | (funext a b c; fun_induction sourceASummand a b c <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, *]; done)
  | (funext a b c; simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def]; done)
  | (simp [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def] <;> rfl; done)
  | (funext v1; unfold sourceASummand ErdosProblems.Erdos1049.PaperR11.sourceASummand <;> simp only [gaussBinom_transport_def, sourceGaussianProduct_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [sourceASummand, ErdosProblems.Erdos1049.PaperR11.sourceASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold sourceASummand ErdosProblems.Erdos1049.PaperR11.sourceASummand <;> simp only [gaussBinom_transport_def, sourceGaussianProduct_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand` is the same function. -/
theorem sourceNormalisedASummand_transport_def : @sourceNormalisedASummand = @ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand := by
  first
  | (rfl; done)
  | (simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold sourceNormalisedASummand ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand; done)
  | (unfold sourceNormalisedASummand ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (ext x; simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def]; done)
  | (funext a; fun_induction sourceNormalisedASummand a <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a; induction a <;> simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a; simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def]; done)
  | (funext a b; fun_induction sourceNormalisedASummand a b <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b; simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def]; done)
  | (funext a b c; fun_induction sourceNormalisedASummand a b c <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, *]; done)
  | (funext a b c; simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def]; done)
  | (simp [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def] <;> rfl; done)
  | (funext v1; unfold sourceNormalisedASummand ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand <;> simp only [gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [sourceNormalisedASummand, ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold sourceNormalisedASummand ErdosProblems.Erdos1049.PaperR11.sourceNormalisedASummand <;> simp only [gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial` is the same function. -/
theorem sourceAWithoutMonomial_transport_def : @sourceAWithoutMonomial = @ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial := by
  first
  | (rfl; done)
  | (simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold sourceAWithoutMonomial ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial; done)
  | (unfold sourceAWithoutMonomial ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (ext x; simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def]; done)
  | (funext a; fun_induction sourceAWithoutMonomial a <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a; induction a <;> simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a; simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def]; done)
  | (funext a b; fun_induction sourceAWithoutMonomial a b <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b; simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def]; done)
  | (funext a b c; fun_induction sourceAWithoutMonomial a b c <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, *]; done)
  | (funext a b c; simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def]; done)
  | (simp [sourceAWithoutMonomial, ErdosProblems.Erdos1049.PaperR11.sourceAWithoutMonomial, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperR11.sourceU` is the same function. -/
theorem sourceU_transport_def : @sourceU = @ErdosProblems.Erdos1049.PaperR11.sourceU := by
  first
  | (rfl; done)
  | (simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold sourceU ErdosProblems.Erdos1049.PaperR11.sourceU; done)
  | (unfold sourceU ErdosProblems.Erdos1049.PaperR11.sourceU <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (ext x; simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def]; done)
  | (funext a; fun_induction sourceU a <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a; induction a <;> simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a; simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def]; done)
  | (funext a b; fun_induction sourceU a b <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b; simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def]; done)
  | (funext a b c; fun_induction sourceU a b c <;> simp only [ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, *]; done)
  | (funext a b c; simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def]; done)
  | (simp [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [sourceU, ErdosProblems.Erdos1049.PaperR11.sourceU, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def] <;> rfl; done)
  | (funext v1; unfold sourceU ErdosProblems.Erdos1049.PaperR11.sourceU <;> simp only [gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand` is the same function. -/
theorem sourceShiftedASummand_transport_def : @sourceShiftedASummand = @ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand := by
  first
  | (rfl; done)
  | (simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold sourceShiftedASummand ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand; done)
  | (unfold sourceShiftedASummand ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand <;> simp only [ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (ext x; simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def]; done)
  | (funext a; fun_induction sourceShiftedASummand a <;> simp only [ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a; induction a <;> simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a; induction a <;> simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a; simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def]; done)
  | (funext a b; fun_induction sourceShiftedASummand a b <;> simp only [ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b; simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def]; done)
  | (funext a b c; fun_induction sourceShiftedASummand a b c <;> simp only [ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def, *]; done)
  | (funext a b c; simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def]; done)
  | (simp [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def] <;> rfl; done)
  | (funext v1; unfold sourceShiftedASummand ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand <;> simp only [gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def] <;> rfl; done)
  | (funext v1 v2; simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def] <;> rfl; done)
  | (funext v1 v2; unfold sourceShiftedASummand ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand <;> simp only [gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; simp only [sourceShiftedASummand, ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand, gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def] <;> rfl; done)
  | (funext v1 v2 v3; unfold sourceShiftedASummand ErdosProblems.Erdos1049.PaperR12.sourceShiftedASummand <;> simp only [gaussBinom_transport_def, sourceGaussianProduct_transport_def, sourceASummand_transport_def, sourceNormalisedASummand_transport_def, sourceAWithoutMonomial_transport_def, sourceU_transport_def] <;> rfl; done)

theorem exists_quadratic_source_height_bound :
    ∃ h : ℝ, ∀ n : ℕ, 1 ≤ n →
      Real.log
          ((max (maxCoeffNat (sourceU n))
            (maxCoeffNat (sourceV n)) : ℕ) : ℝ) ≤
        h * (n : ℝ) ^ 2 := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos1049.PaperCompleteR21.exists_quadratic_source_height_bound

theorem maxPairHeight_source_eq (n : ℕ) :
    maxPairHeight sourceU sourceV n =
      ((max (maxCoeffNat (sourceU n))
        (maxCoeffNat (sourceV n)) : ℕ) : ℝ) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos1049.PaperCompleteR21.maxPairHeight_source_eq n

end PalomarCorpus.E1049.PaperStructuresQ
