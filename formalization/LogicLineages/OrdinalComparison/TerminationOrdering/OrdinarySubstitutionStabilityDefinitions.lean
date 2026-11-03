module
public import LogicLineages.OrdinalComparison.TerminationOrdering.SuccessfulApplicationSourceProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStability
open Source Source.SourceMarkedSyntax Source.SourceMarkedBinding RecursiveComparison

def markedMap {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : Substitution Symbol arity Gamma Delta) : MarkedSubstitution Symbol arity Gamma Delta :=
  fun v => embed (theta v)

def substitutePacked {Symbol : Type} {arity : Symbol → Nat} {Gamma Delta : List Ty}
    (theta : Substitution Symbol arity Gamma Delta) (p : Packed Symbol arity Gamma) : Packed Symbol arity Delta :=
  ⟨p.1,substituteTerm p.2 (markedMap theta)⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.OrdinarySubstitutionStability
