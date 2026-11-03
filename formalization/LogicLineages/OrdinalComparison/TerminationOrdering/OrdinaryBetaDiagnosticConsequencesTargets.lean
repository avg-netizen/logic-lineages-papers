module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaTransitivityDiagnosticProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitutionDefinitions

@[expose] public section
/-! Exact consequences for the SAME checked source-Term witness. No alternative
marking convention, added comparison rule or source-definition edit. -/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaDiagnosticConsequencesTargets
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport RecursiveComparison
open OrdinaryBetaTransitivityDiagnostic

def ActualConfinedWitness : Prop :=
  ConfinedOrdinarySubstitution.ConfinedWeak above pOriginal tOriginal ∧
  LiteralContexts.ConfinedStrict above tOriginal uOriginal ∧
  ¬ConfinedOrdinarySubstitution.ConfinedWeak above pOriginal uOriginal

def ActualStrictChain : Prop :=
  Strict Nat arity above [] ⟨.ground,embed pOriginal⟩ ⟨.ground,embed tOriginal⟩ ∧
  Strict Nat arity above [] ⟨.ground,embed tOriginal⟩ ⟨.ground,embed uOriginal⟩ ∧
  ¬Strict Nat arity above [] ⟨.ground,embed pOriginal⟩ ⟨.ground,embed uOriginal⟩

def ActualStrictWeakRefutation : Prop :=
  ¬OrdinaryTransitivityTargets.ActualStrictWeakCompatibility

def ActualRawEndpointRefutation : Prop :=
  ¬SourceFinalTransitivityTargets.ActualOriginalEndpointTransitivity

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinaryBetaDiagnosticConsequencesTargets
