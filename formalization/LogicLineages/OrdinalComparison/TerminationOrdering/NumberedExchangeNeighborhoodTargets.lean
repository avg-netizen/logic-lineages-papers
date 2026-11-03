module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodTargets
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedPrimaryExchange NumberedExchangeNeighborhood

def ActualTypedListReconstruction : Prop := ∀ (Symbol : Type) (arity : Symbol → Nat) (Gamma types : List Ty) (values : List (Packed Symbol arity Gamma)) (args : AuxArguments Symbol arity Gamma types),
  argumentsFromList types values=some args ↔ argumentList args=values

def ActualTermNeighborhood : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (tau : Ty) (q r : AuxTerm Symbol arity Gamma tau),
  r∈neighbors symbols S q ↔ Exchange Symbol arity symbols S Gamma ⟨tau,q⟩ ⟨tau,r⟩

def ActualArgumentNeighborhood : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma types : List Ty) (args target : AuxArguments Symbol arity Gamma types),
  target∈argumentNeighbors symbols S args ↔ ArgumentExchange Symbol arity symbols S Gamma types args target

def ActualExchangeTest : Prop := ∀ (Symbol : Type) (_ : DecidableEq Symbol) (arity : Symbol → Nat) (symbols : List Symbol) (S : List Ty),
  SubtypeClosed (fun tau => tau∈S) → ∀ (Gamma : List Ty) (q r : Packed Symbol arity Gamma),
  exchangeTest symbols S q r=true ↔ Exchange Symbol arity symbols S Gamma q r

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedExchangeNeighborhoodTargets
