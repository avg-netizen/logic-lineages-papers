module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInverseApplicationAccessibilityDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInverseApplicationAccessibilityTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative
open NumberedQuotientPaths NumberedQuotientApplication NumberedWindowTraces

def ActualTypedSuccessorWitness : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (tau : Ty)
      (q : AuxTerm (Fin n) arity Gamma tau) (y : Nat), InUniverse symbols S q →
    PositivePath (QuotientEdge n arity symbols S above Gamma) (representativeCode symbols S ⟨tau,q⟩) y →
    ∃ r : AuxTerm (Fin n) arity Gamma tau, InUniverse symbols S r ∧
      representativeCode symbols S ⟨tau,r⟩ = y ∧
      ∃ count : Nat, 0 < count ∧ WindowTypedTrace (Fin n) arity symbols S above Gamma tau count q r

def ActualInverseApplicationAccessibility : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (above : Fin n → Fin n → Prop) (Gamma : List Ty) (sigma tau : Ty)
      (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a : AuxTerm (Fin n) arity Gamma sigma),
    InUniverse symbols S f → InUniverse symbols S a →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Gamma) source successor)
      (representativeCode symbols S (applicationPacked f a)) →
    Acc (fun successor source => PositivePath (QuotientEdge n arity symbols S above Gamma) source successor)
      (representativeCode symbols S ⟨.arrow sigma tau,f⟩)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedInverseApplicationAccessibilityTargets
