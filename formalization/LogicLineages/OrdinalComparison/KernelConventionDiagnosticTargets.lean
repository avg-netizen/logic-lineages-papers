module
public import LogicLineages.OrdinalComparison.KernelConventionDiagnosticDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.KernelConventionDiagnostic.Targets

/-- Exact current-state/budget diagnostic. No principal-kernel reachability
or counterexample to a whole paper theorem is asserted. -/
def ExactSuccessorTailDiscrepancy : Prop := ∀ b : Nat, 2 ≤ b →
  wholeStep (Ordinal.omega0+1) b = Ordinal.omega0 ∧
  limitStep (Ordinal.omega0+1) b = (b : Ordinal) ∧
  limitStep (Ordinal.omega0+1) b < Ordinal.omega0 ∧
  wholeStep (Ordinal.omega0+1) b ≠ limitStep (Ordinal.omega0+1) b

/-- Same state, actual compensated budget, arbitrary retained mass. This is a
transition-level semantic distinction, not a source-intent or reachability claim. -/
def ActualCompensatedDiscrepancy : Prop := ∀ c : Nat,
  2 ≤ budget c ∧
  actualControlledStep (compensatedPrefixControl c) (Ordinal.omega0+1) = (budget c : Ordinal) ∧
  wholeStep (Ordinal.omega0+1) (budget c) = Ordinal.omega0 ∧
  actualControlledStep (compensatedPrefixControl c) (Ordinal.omega0+1) ≠
    wholeStep (Ordinal.omega0+1) (budget c)

end LogicLineages.OrdinalComparison.KernelConventionDiagnostic.Targets
