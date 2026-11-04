module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationPathsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationPathsTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPaths NumberedQuotientApplication

def ActualCountedFunctionApplication : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty)
    (sigma tau : Ty) (f g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma),
    InUniverse symbols S f → InUniverse symbols S g → InUniverse symbols S a →
    ∀ count : Nat,
    CountedPath (QuotientEdge n arity symbols S above Gamma) count
      (representativeCode symbols S ⟨.arrow sigma tau,f⟩) (representativeCode symbols S ⟨.arrow sigma tau,g⟩) →
    CountedPath (QuotientEdge n arity symbols S above Gamma) count
      (representativeCode symbols S (applicationPacked f a)) (representativeCode symbols S (applicationPacked g a))

def ActualPositiveFunctionApplication : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty),
    SubtypeClosed (fun t => t ∈ S) → ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty)
    (sigma tau : Ty) (f g : AuxTerm (Fin n) arity Gamma (.arrow sigma tau))
    (a : AuxTerm (Fin n) arity Gamma sigma),
    InUniverse symbols S f → InUniverse symbols S g → InUniverse symbols S a →
    PositivePath (QuotientEdge n arity symbols S above Gamma)
      (representativeCode symbols S ⟨.arrow sigma tau,f⟩) (representativeCode symbols S ⟨.arrow sigma tau,g⟩) →
    PositivePath (QuotientEdge n arity symbols S above Gamma)
      (representativeCode symbols S (applicationPacked f a)) (representativeCode symbols S (applicationPacked g a))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientApplicationPathsTargets
