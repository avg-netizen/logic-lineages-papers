module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverseDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverseTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedFiniteUniverse

def ActualHeadWindow : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty),SubtypeClosed (fun t => t∈S) → ∀ f : Head Symbol,
    f∈headWindow arity symbols S ↔ HeadInWindow arity symbols S f

def ActualRepresentationConfinement : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (K : Ty → Prop) (H : Head Symbol → Prop) (n : Nat) (Gamma : List Ty) (tau : Ty)
    (q : MarkedTerm Symbol arity Gamma tau) (Q : AuxTerm Symbol arity Gamma tau),Represents Symbol arity n Gamma tau q Q →
    (typesAllowed K q ↔ auxTypesAllowed K Q) ∧ (headsAllowed H q ↔ auxHeadsAllowed H Q)

def ActualArgumentConfinement : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (K : Ty → Prop) (H : Head Symbol → Prop) (n : Nat) (Gamma types : List Ty)
    (args : Arguments Symbol arity Gamma types) (values : AuxArguments Symbol arity Gamma types),ArgumentsRepresent Symbol arity n Gamma types args values →
    (argumentTypesAllowed K args ↔ auxArgumentTypesAllowed K values) ∧ (argumentsAllowed H args ↔ auxArgumentsAllowed H values)

def ActualUnmarkedHeadWindow : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (Gamma : List Ty) (tau : Ty) (q : MarkedTerm Symbol arity Gamma tau),
    SourceUnmarked.Unmarked Symbol arity Gamma q → typesAllowed (fun t => t∈S) q →
    headsAllowed (RankedCovered symbols) q → headsAllowed (HeadInWindow arity symbols S) q

def ActualUnmarkedUniverse : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat)
    (symbols : List Symbol) (S : List Ty) (n : Nat) (Gamma : List Ty) (tau : Ty)
    (q : MarkedTerm Symbol arity Gamma tau) (Q : AuxTerm Symbol arity Gamma tau),
    SourceUnmarked.Unmarked Symbol arity Gamma q → typesAllowed (fun t => t∈S) q →
    headsAllowed (RankedCovered symbols) q → Represents Symbol arity n Gamma tau q Q → InUniverse symbols S Q

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedFiniteUniverseTargets
