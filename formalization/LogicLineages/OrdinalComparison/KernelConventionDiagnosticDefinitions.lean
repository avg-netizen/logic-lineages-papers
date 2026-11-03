module
public import LogicLineages.OrdinalComparison.SuffixKernelDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelConventionDiagnostic
/-- Literal greatest predecessor below the whole current suffix. -/
noncomputable def wholeStep (a : Ordinal) (b : Nat) : Ordinal := actualMaximumPredecessor a b
/-- Companion convention: remove the finite part before taking the maximum. -/
noncomputable def limitStep (a : Ordinal) (b : Nat) : Ordinal := actualMaximumPredecessor (actualLimitPart a) b
noncomputable def budget (c : Nat) : Nat :=
  Phi (c+actualOrdinalNorm (Ordinal.omega0+1))-c
end LogicLineages.OrdinalComparison.KernelConventionDiagnostic
