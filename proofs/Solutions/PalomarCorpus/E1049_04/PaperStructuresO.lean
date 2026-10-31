/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos1049.PaperR16.LambertBasic
import ErdosProblems.Erdos1049.PaperR20.CoefficientPencil
import ErdosProblems.Erdos1049.PaperR20.FinitePencilProposition
import ErdosProblems.Erdos1049.QBinomialUnitIdentity
import Solutions.PalomarCorpus.E1049_04.Statement

open Matrix
open Polynomial
open scoped BigOperators
open Filter
open Topology
open Finset

/- Copyright (c) 2026 Will Cook. Released under the Apache 2.0 license. -/

namespace PalomarCorpus.E1049.PaperStructuresO

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.gaussBinom` is the same function. -/
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
/-- The local copy of `ErdosProblems.Erdos1049.PaperR20.coefficientRPoly` is the same function. -/
theorem coefficientRPoly_transport_def : @coefficientRPoly = @ErdosProblems.Erdos1049.PaperR20.coefficientRPoly := by
  first
  | (rfl; done)
  | (simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold coefficientRPoly ErdosProblems.Erdos1049.PaperR20.coefficientRPoly; done)
  | (unfold coefficientRPoly ErdosProblems.Erdos1049.PaperR20.coefficientRPoly <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (ext x; simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def]; done)
  | (funext a; fun_induction coefficientRPoly a <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a; induction a <;> simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a; induction a <;> simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a; simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def]; done)
  | (funext a b; fun_induction coefficientRPoly a b <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b; simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def]; done)
  | (funext a b c; fun_induction coefficientRPoly a b c <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def, *]; done)
  | (funext a b c; simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def]; done)
  | (simp [coefficientRPoly, ErdosProblems.Erdos1049.PaperR20.coefficientRPoly, gaussBinom_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly` is the same function. -/
theorem coefficientMomentPoly_transport_def : @coefficientMomentPoly = @ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly := by
  first
  | (rfl; done)
  | (simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold coefficientMomentPoly ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly; done)
  | (unfold coefficientMomentPoly ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (ext x; simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def]; done)
  | (funext a; fun_induction coefficientMomentPoly a <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a; induction a <;> simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a; induction a <;> simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a; induction a <;> simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a; simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def]; done)
  | (funext a b; fun_induction coefficientMomentPoly a b <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b; simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def]; done)
  | (funext a b c; fun_induction coefficientMomentPoly a b c <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, *]; done)
  | (funext a b c; simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def]; done)
  | (simp [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def]; done)
  | (set_option smartUnfolding false in with_unfolding_all rfl; done)
  | (funext v1; simp only [coefficientMomentPoly, ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly, gaussBinom_transport_def, coefficientRPoly_transport_def] <;> rfl; done)
  | (funext v1; unfold coefficientMomentPoly ErdosProblems.Erdos1049.PaperR20.coefficientMomentPoly <;> simp only [gaussBinom_transport_def, coefficientRPoly_transport_def] <;> rfl; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly` is the same function. -/
theorem coefficientAlphaPoly_transport_def : @coefficientAlphaPoly = @ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly := by
  first
  | (rfl; done)
  | (simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold coefficientAlphaPoly ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly; done)
  | (unfold coefficientAlphaPoly ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (ext x; simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def]; done)
  | (funext a; fun_induction coefficientAlphaPoly a <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a; induction a <;> simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a; induction a <;> simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a; induction a <;> simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a; simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def]; done)
  | (funext a b; fun_induction coefficientAlphaPoly a b <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b; simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def]; done)
  | (funext a b c; fun_induction coefficientAlphaPoly a b c <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, *]; done)
  | (funext a b c; simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def]; done)
  | (simp [coefficientAlphaPoly, ErdosProblems.Erdos1049.PaperR20.coefficientAlphaPoly, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def]; done)

set_option maxRecDepth 8000 in
/-- The local copy of `ErdosProblems.Erdos1049.PaperR20.coefficientAlpha` is the same function. -/
theorem coefficientAlpha_transport_def : @coefficientAlpha = @ErdosProblems.Erdos1049.PaperR20.coefficientAlpha := by
  first
  | (rfl; done)
  | (simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def]; done)
  | (with_unfolding_all rfl; done)
  | (unfold coefficientAlpha ErdosProblems.Erdos1049.PaperR20.coefficientAlpha; done)
  | (unfold coefficientAlpha ErdosProblems.Erdos1049.PaperR20.coefficientAlpha <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (ext x; simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def]; done)
  | (funext a; rfl; done)
  | (funext a; simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def]; done)
  | (funext a; fun_induction coefficientAlpha a <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a; induction a <;> simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a; induction a <;> simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a; induction a <;> simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a; simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def]; done)
  | (funext a b; rfl; done)
  | (funext a b; simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def]; done)
  | (funext a b; fun_induction coefficientAlpha a b <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b; induction b <;> simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b; induction a generalizing b <;> simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b; induction b generalizing a <;> simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b; simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def]; done)
  | (funext a b c; rfl; done)
  | (funext a b c; simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def]; done)
  | (funext a b c; fun_induction coefficientAlpha a b c <;> simp only [ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b c; induction c <;> simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b c; induction a generalizing b c <;> simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b c; induction b generalizing a c <;> simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp only [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b c; induction c generalizing a b <;> simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def, *]; done)
  | (funext a b c; simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def]; done)
  | (simp [coefficientAlpha, ErdosProblems.Erdos1049.PaperR20.coefficientAlpha, gaussBinom_transport_def, coefficientRPoly_transport_def, coefficientMomentPoly_transport_def, coefficientAlphaPoly_transport_def]; done)

theorem coefficientPencil_finitePencil {p : ℝ} (hp : 1 < p) :
    (∀ N : ℕ, N ≤ 8 →
      (coefficientAlphaMatrix p N).PosDef ∧
        (coefficientPencilPoly p N).Splits ∧
        ∀ x : ℝ, (coefficientPencilPoly p N).IsRoot x → x < lambert (1 / p)) ∧
    (∀ N : ℕ, N + 1 ≤ 8 →
      ∃ (large : Fin (N + 1) → ℝ) (small : Fin N → ℝ),
        Antitone large ∧ Antitone small ∧
        (coefficientPencilPoly p (N + 1)).roots = Multiset.map large Finset.univ.val ∧
        (coefficientPencilPoly p N).roots = Multiset.map small Finset.univ.val ∧
        ∀ i : Fin N, small i ≤ large i.castSucc ∧ large i.succ ≤ small i) := by
  set_option smartUnfolding false in
  exact @ErdosProblems.Erdos1049.PaperR20.coefficientPencil_finitePencil p hp

end PalomarCorpus.E1049.PaperStructuresO
