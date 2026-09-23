/-
Copyright (c) 2026 Will Cook. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Will Cook
-/
import Mathlib
import ErdosProblems.Erdos269.CofinalWindowEscapeEquivalence
import ErdosProblems.Erdos269.PaperCompleteR20.OcticEscapeWhole
import Solutions.PalomarCorpus.E269_11.Statement

namespace PalomarCorpus.E269.WindowEscapeEquivalence

lemma leastPositiveResidue_fun_eq :
    leastPositiveResidue = ErdosProblems.Erdos269.leastPositiveResidue := by
  funext C x
  simp [leastPositiveResidue, ErdosProblems.Erdos269.leastPositiveResidue]

lemma windowBase_fun_eq :
    windowBase = ErdosProblems.Erdos269.windowBase := by
  funext b lo len
  induction len with
  | zero =>
    simp [windowBase, ErdosProblems.Erdos269.windowBase]
  | succ n ih =>
    simp [windowBase, ErdosProblems.Erdos269.windowBase, ih]

lemma windowForcing_fun_eq :
    windowForcing = ErdosProblems.Erdos269.windowForcing := by
  funext b e lo len
  induction len with
  | zero =>
    simp [windowForcing, ErdosProblems.Erdos269.windowForcing]
  | succ n ih =>
    simp [windowForcing, ErdosProblems.Erdos269.windowForcing, ih]

lemma smooth3Val_fun_eq :
    smooth3Val = ErdosProblems.Erdos269.smooth3Val := by
  funext p q r i j k
  simp [smooth3Val, ErdosProblems.Erdos269.smooth3Val]

lemma strictSmoothExponents_source_eq (p q r x : ℕ) :
    strictSmoothExponents p q r x =
      ErdosProblems.Erdos269.strictSmoothExponents p q r x := by
  ext e
  simp [strictSmoothExponents, ErdosProblems.Erdos269.strictSmoothExponents,
    smooth3Val_fun_eq]

lemma strictSmoothShell_source_eq (p q r x y : ℕ) :
    strictSmoothShell p q r x y =
      ErdosProblems.Erdos269.strictSmoothShell p q r x y := by
  simp [strictSmoothShell, ErdosProblems.Erdos269.strictSmoothShell,
    strictSmoothExponents_source_eq]

lemma dyadicSmoothShell235_source_eq (a : ℕ) :
    dyadicSmoothShell235 a = ErdosProblems.Erdos269.dyadicSmoothShell235 a := by
  simp [dyadicSmoothShell235, ErdosProblems.Erdos269.dyadicSmoothShell235,
    strictSmoothShell_source_eq]

lemma dyadicBeforeThresholdCount235_source_eq (p a : ℕ) :
    dyadicBeforeThresholdCount235 p a =
      ErdosProblems.Erdos269.dyadicBeforeThresholdCount235 p a := by
  simp [dyadicBeforeThresholdCount235,
    ErdosProblems.Erdos269.dyadicBeforeThresholdCount235,
    dyadicSmoothShell235_source_eq, smooth3Val_fun_eq]

lemma dyadicBlockBase235_fun_eq :
    dyadicBlockBase235 = ErdosProblems.Erdos269.dyadicBlockBase235 := by
  funext a
  unfold dyadicBlockBase235 ErdosProblems.Erdos269.dyadicBlockBase235
  -- In this family file the abbreviation makes `simp` close the goal outright; in the
  -- generated problem-level adapter the copied definition leaves the four radix cases,
  -- so the case split runs only when a goal remains.
  simp [DyadicInternalPower, ErdosProblems.Erdos269.DyadicInternalPower]
  all_goals
    by_cases h5 : ∃ e, 2 ^ a < 5 ^ e ∧ 5 ^ e < 2 ^ (a + 1)
    · by_cases h3 : ∃ e, 2 ^ a < 3 ^ e ∧ 3 ^ e < 2 ^ (a + 1)
      · simp [h5, h3]
      · simp [h5, h3]
    · by_cases h3 : ∃ e, 2 ^ a < 3 ^ e ∧ 3 ^ e < 2 ^ (a + 1)
      · simp [h5, h3]
      · simp [h5, h3]

lemma dyadicOrderedBlockDigit235_fun_eq :
    dyadicOrderedBlockDigit235 = ErdosProblems.Erdos269.dyadicOrderedBlockDigit235 := by
  funext a
  simp [dyadicOrderedBlockDigit235, ErdosProblems.Erdos269.dyadicOrderedBlockDigit235,
    dyadicSmoothShell235_source_eq, dyadicBeforeThresholdCount235_source_eq]

lemma CofinalLocalWindowEscape_fun_eq :
    CofinalLocalWindowEscape = ErdosProblems.Erdos269.CofinalLocalWindowEscape := by
  funext b m sb
  simp [CofinalLocalWindowEscape, ErdosProblems.Erdos269.CofinalLocalWindowEscape,
    windowBase_fun_eq, windowForcing_fun_eq, leastPositiveResidue_fun_eq]

lemma ActualCofinalLocalWindowEscape_prop_eq :
    ActualCofinalLocalWindowEscape = ErdosProblems.Erdos269.ActualCofinalLocalWindowEscape := by
  -- In this family file the abbreviation makes the two propositions definitionally equal; in the
  -- generated problem-level adapter the Statement module supplies genuine copies of the escape
  -- predicate, the radix word, the ordered digit and the short bound, so each is transported.
  first
  | rfl
  | simp only [ActualCofinalLocalWindowEscape,
      ErdosProblems.Erdos269.ActualCofinalLocalWindowEscape,
      CofinalLocalWindowEscape_fun_eq, dyadicBlockBase235_fun_eq,
      dyadicOrderedBlockDigit235_fun_eq, bridgeWidth,
      ErdosProblems.Erdos269.bridgeWidth]

theorem actualCofinalLocalWindowEscape_iff_irrational_value :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 0) := by
  rw [ActualCofinalLocalWindowEscape_prop_eq]
  convert ErdosProblems.Erdos269.actualCofinalLocalWindowEscape_iff_irrational_value
  all_goals try rfl

theorem actualCofinalLocalWindowEscape_iff :
    ActualCofinalLocalWindowEscape ↔ Irrational (dyadicShellTsumTailR235 1) := by
  rw [ActualCofinalLocalWindowEscape_prop_eq]
  convert ErdosProblems.Erdos269.actualCofinalLocalWindowEscape_iff
  all_goals try rfl

theorem cofinalLocalWindowEscape_of_irrational
    (h : Irrational (dyadicShellTsumTailR235 1)) :
    ActualCofinalLocalWindowEscape := by
  rw [ActualCofinalLocalWindowEscape_prop_eq]
  convert ErdosProblems.Erdos269.cofinalLocalWindowEscape_of_irrational h
  all_goals try rfl

theorem cofinalLocalWindowEscape_of_irrational_of_quadratic
    (h : Irrational (dyadicShellTsumTailR235 1)) (sb : ℕ → ℕ → ℕ) (c : ℕ → ℕ)
    (hsb : ∀ B n, sb B n ≤ c B * (n + 1) ^ 2) :
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 sb := by
  convert ErdosProblems.Erdos269.cofinalLocalWindowEscape_of_irrational_of_quadratic
    h sb c hsb
  all_goals try exact CofinalLocalWindowEscape_fun_eq

theorem exists_reducedCarry_of_value_eq_rat
    {p q : ℤ} (hq : 0 < q)
    (hval : dyadicShellTsumTailR235 1 = (p : ℝ) / (q : ℝ)) :
    ∃ (B a₀ : ℕ) (d : ℕ → ℤ), 0 < B ∧ Nat.Coprime B 30 ∧
      (∀ n, a₀ ≤ n →
        d (n + 1) = (dyadicBlockBase235 n : ℤ) * d n
          - (B : ℤ) * (dyadicOrderedBlockDigit235 n : ℤ)) ∧
      (∀ n, a₀ ≤ n → 0 < d n) ∧
      (∀ n, a₀ ≤ n → Int.natAbs (d n) ≤ B * bridgeWidth n) := by
  convert ErdosProblems.Erdos269.exists_reducedCarry_of_value_eq_rat hq hval
  all_goals try rfl

theorem trueNormalizedState_window (lo len : ℕ) :
    trueNormalizedState (lo + len)
      = ((windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len : ℤ) : ℝ)
          * trueNormalizedState lo
        - ((windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
              (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len : ℤ) : ℝ) := by
  convert ErdosProblems.Erdos269.trueNormalizedState_window lo len
  all_goals
    try exact windowBase_fun_eq
    try exact windowForcing_fun_eq

theorem near_integer_of_residue_le_general
    (B lo len K : ℕ) (hB : 0 < B)
    (hKle : B * bridgeWidth (lo + len) ≤ K)
    (hres : leastPositiveResidue
        (Int.natAbs (windowBase (fun n => (dyadicBlockBase235 n : ℤ)) lo len))
        (-((B : ℤ) * windowForcing (fun n => (dyadicBlockBase235 n : ℤ))
             (fun n => (dyadicOrderedBlockDigit235 n : ℤ)) lo len))
      ≤ K) :
    ∃ k : ℤ, |(B : ℝ) * trueNormalizedState lo - (k : ℝ)|
      ≤ ((K : ℕ) : ℝ) / 2 ^ len := by
  convert ErdosProblems.Erdos269.near_integer_of_residue_le_general
    B lo len K hB hKle
    (by simpa [leastPositiveResidue_fun_eq, windowBase_fun_eq, windowForcing_fun_eq,
      dyadicBlockBase235_fun_eq, dyadicOrderedBlockDigit235_fun_eq] using hres)
  all_goals
    try exact windowBase_fun_eq
    try exact windowForcing_fun_eq
    try exact dyadicBlockBase235_fun_eq
    try exact dyadicOrderedBlockDigit235_fun_eq

theorem exists_pow_gt_quadratic (c lo : ℕ) :
    ∃ len : ℕ, 0 < len ∧ c * (lo + len + 1) ^ 2 < 2 ^ len := by
  convert ErdosProblems.Erdos269.exists_pow_gt_quadratic c lo
  all_goals try rfl

lemma longPaperCap_fun_eq :
    longPaperCap = ErdosProblems.Erdos269.PaperR7.longPaperCap :=
  rfl

lemma shortPaperCap_fun_eq :
    shortPaperCap = ErdosProblems.Erdos269.PaperCompleteR20.shortPaperCap :=
  rfl

theorem octic_escape_whole :
    (∀ G : ℕ → ℕ → ℕ,
      (∀ B a, 0 < B → longPaperCap B a ≤ G B a) →
      (∀ B, 0 < B → Filter.Tendsto
        (fun a : ℕ => (G B a : ℝ) / (8 : ℝ) ^ a) Filter.atTop (nhds 0)) →
      (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 G ↔
        Irrational (dyadicShellTsumTailR235 0))) ∧
    (∀ B : ℕ, Filter.Tendsto
      (fun a : ℕ => (longPaperCap B a : ℝ) / (8 : ℝ) ^ a) Filter.atTop (nhds 0)) ∧
    (∀ B a : ℕ, longPaperCap B a ≤ shortPaperCap B a) ∧
    (∀ B : ℕ, Filter.Tendsto
      (fun a : ℕ => (shortPaperCap B a : ℝ) / (8 : ℝ) ^ a) Filter.atTop (nhds 0)) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 longPaperCap ↔
      Irrational (dyadicShellTsumTailR235 0)) ∧
    (CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 shortPaperCap ↔
      Irrational (dyadicShellTsumTailR235 0)) ∧
    CofinalLocalWindowEscape dyadicBlockBase235 dyadicOrderedBlockDigit235 (fun _ _ => 0) := by
  simpa only [ErdosProblems.Erdos269.PaperR7.paperSeries235_eq_shellTsum,
    CofinalLocalWindowEscape_fun_eq, dyadicBlockBase235_fun_eq,
    dyadicOrderedBlockDigit235_fun_eq, longPaperCap_fun_eq, shortPaperCap_fun_eq] using
    ErdosProblems.Erdos269.PaperCompleteR20.octic_escape_whole

end PalomarCorpus.E269.WindowEscapeEquivalence
