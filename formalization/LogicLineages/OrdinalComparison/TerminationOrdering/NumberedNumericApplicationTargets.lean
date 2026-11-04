module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationTargets
open Source NumberedRewriteSyntax NumberedFiniteUniverse NumberedLeastCodeRepresentative NumberedTypedCarrier NumberedQuotientApplication NumberedNumericApplication

def ActualCanonicalApplicationSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (Gamma : List Ty) (sigma tau : Ty) (x y z : Nat),
    canonicalApplication n arity symbols S Gamma sigma tau x y = some z →
      ∃ (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a : AuxTerm (Fin n) arity Gamma sigma),
        InUniverse symbols S f ∧ InUniverse symbols S a ∧
        representativeCode symbols S ⟨.arrow sigma tau,f⟩ = x ∧ representativeCode symbols S ⟨sigma,a⟩ = y ∧
        representativeCode symbols S (applicationPacked f a) = z ∧
        typedCanonicalCarrierTest n arity symbols S Gamma tau z = true

def ActualCanonicalApplicationCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun t => t ∈ S) →
    ∀ (Gamma : List Ty) (sigma tau : Ty)
      (f : AuxTerm (Fin n) arity Gamma (.arrow sigma tau)) (a : AuxTerm (Fin n) arity Gamma sigma),
      InUniverse symbols S f → InUniverse symbols S a →
      canonicalApplication n arity symbols S Gamma sigma tau
        (representativeCode symbols S ⟨.arrow sigma tau,f⟩) (representativeCode symbols S ⟨sigma,a⟩) =
        some (representativeCode symbols S (applicationPacked f a))

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericApplicationTargets
