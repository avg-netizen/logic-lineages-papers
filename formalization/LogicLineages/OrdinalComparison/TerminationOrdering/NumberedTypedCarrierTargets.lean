module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrierTargets
open Source NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowEquivalence NumberedLeastCodeRepresentative NumberedTypedCarrier

def ActualTypedRepresentativeAttained : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun tau => tau ∈ S) →
    ∀ (Gamma : List Ty) (q : Packed (Fin n) arity Gamma), InUniverse symbols S q.2 →
    ∃ r : Packed (Fin n) arity Gamma, WindowPrimary (Fin n) arity symbols S Gamma q r ∧
      r.1 = q.1 ∧ InUniverse symbols S r.2 ∧ representativeCode symbols S q = packedNumber r

def ActualTypedCanonicalCarrier : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun tau => tau ∈ S) →
    ∀ (Gamma : List Ty) (tau : Ty) (value : Nat),
    (typedCanonicalCarrierTest n arity symbols S Gamma tau value = true ↔
      ∃ q : Packed (Fin n) arity Gamma, InUniverse symbols S q.2 ∧ q.1 = tau ∧
        representativeCode symbols S q = value)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedCarrierTargets
