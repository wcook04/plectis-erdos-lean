module

public import ErdosProblems.Erdos243.PaperCompleteR9.AdaptiveCoefficients
public import ErdosProblems.Erdos243.PaperCompleteR9.CoefficientHeight
public import ErdosProblems.Erdos243.PaperCompleteR9.PolynomialCorrections
public import ErdosProblems.Erdos243.PaperCompleteR9.ValuationPayment
public import ErdosProblems.Erdos243.PaperCompleteR9.WeightedRecurrence

@[expose] public section

/-!
# R9 coefficient and recurrence packet aggregate

This aggregate imports the five R9 coefficient and recurrence modules. Their
dependencies are reached transitively. It neither restores the historical R8
archive nor imports the conditional cubic chain.
-/
