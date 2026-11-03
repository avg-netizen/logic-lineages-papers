module
public import LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnosticDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnosticTargets
open Source Source.SourceMarkedSyntax RecursiveComparison FiniteOrdinaryBetaDiagnostic

def ActualFinitePrecedence : Prop :=
  Transitive above ∧ (∀ f,¬above f f) ∧
  (∀ f g,f≠g → above f g ∨ above g f) ∧
  WellFounded (fun f g => above g f)

def ActualFiniteOrdinarySteps : Prop :=
  Weak (Fin 4) arity above [] ⟨.ground,embed pOriginal⟩ ⟨.ground,embed tOriginal⟩ ∧
  Strict (Fin 4) arity above [] ⟨.ground,embed tOriginal⟩ ⟨.ground,embed uOriginal⟩

def ActualFiniteOrdinaryFailure : Prop :=
  ¬Weak (Fin 4) arity above [] ⟨.ground,embed pOriginal⟩ ⟨.ground,embed uOriginal⟩

def ActualFiniteConfinedWitness : Prop :=
  ConfinedOrdinarySubstitution.ConfinedWeak above pOriginal tOriginal ∧
  LiteralContexts.ConfinedStrict above tOriginal uOriginal ∧
  ¬ConfinedOrdinarySubstitution.ConfinedWeak above pOriginal uOriginal

end LogicLineages.OrdinalComparison.TerminationOrdering.FiniteOrdinaryBetaDiagnosticTargets
