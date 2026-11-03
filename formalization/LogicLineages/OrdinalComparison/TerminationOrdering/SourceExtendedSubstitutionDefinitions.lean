module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedEliminationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStabilitySupportProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitution
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison

def substitutePacked {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : MarkedSubstitution Symbol arity Gamma Delta) (p : Packed Symbol arity Gamma) : Packed Symbol arity Delta :=
  ⟨p.1,substituteTerm p.2 theta⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.SourceExtendedSubstitution
