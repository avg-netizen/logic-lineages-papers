module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticTargets
open Source Source.SourceMarkedSyntax RecursiveComparison OrdinaryBetaTransitivityDiagnostic

def ActualOrdinarySteps : Prop :=
  Weak Nat arity above [] ⟨.ground,embed pOriginal⟩ ⟨.ground,embed tOriginal⟩ ∧
  Strict Nat arity above [] ⟨.ground,embed tOriginal⟩ ⟨.ground,embed uOriginal⟩

def ActualOrdinaryFailure : Prop :=
  ¬Weak Nat arity above [] ⟨.ground,embed pOriginal⟩ ⟨.ground,embed uOriginal⟩

def ActualWeakTransitivityRefutation : Prop :=
  ¬OrdinaryTransitivityTargets.ActualOriginalTransitivity

def ActualWeakStrictRefutation : Prop :=
  ¬OrdinaryTransitivityTargets.ActualWeakStrictCompatibility

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticTargets
