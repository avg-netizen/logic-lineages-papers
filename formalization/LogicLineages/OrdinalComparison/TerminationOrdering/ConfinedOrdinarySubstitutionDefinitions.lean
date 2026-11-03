module
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OriginalInputDecisionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ComparisonFreeVariablesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.LiteralContextsDefinitions
public import LogicLineages.OrdinalComparison.SourceFreeOccurrencesProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitution
open Source Source.SourceMarkedSyntax Source.SourceTypeSupport RecursiveComparison

/-- Literal source06 weak confinement at an arbitrary ordinary typed context.
The historical NativeCarrier.ConfinedWeak specializes to closed arrows. -/
def ConfinedWeak {Symbol : Type} {arity : Symbol → Nat} {Gamma : List Ty} {tau : Ty}
    (above : Symbol → Symbol → Prop) (s t : Term Symbol arity Gamma tau) : Prop :=
  Weak Symbol arity above Gamma ⟨tau,embed s⟩ ⟨tau,embed t⟩ ∧ typeSupport t ⊆ typeSupport s

end LogicLineages.OrdinalComparison.TerminationOrdering.ConfinedOrdinarySubstitution
