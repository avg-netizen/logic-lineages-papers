module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCarrierTargets
open QuotientDirectCarrier

def ActualListCarrier : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Source.Ty), SubtypeClosed (fun tau => tau ∈ S) → ∀ (Gamma : List Source.Ty) (values : List Nat), listCarrierTest n arity symbols S Gamma values = true ↔ ∀ x ∈ values, ∃ q : NumberedRewriteReduction.Packed (Fin n) arity Gamma, NumberedFiniteUniverse.InUniverse symbols S q.2 ∧ NumberedLeastCodeRepresentative.representativeCode symbols S q = x

def ActualPositivePathCarrier : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Source.Ty), SubtypeClosed (fun tau => tau ∈ S) → ∀ (Gamma : List Source.Ty) (table : Fin n → Fin n → Bool) (x y : Nat), QuotientDominationCertificates.relation n arity symbols S Gamma table x y → NumberedNumericCarrier.canonicalCarrierTest n arity symbols S Gamma x = true ∧ NumberedNumericCarrier.canonicalCarrierTest n arity symbols S Gamma y = true

def ActualDirectCarrierPreservation : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Source.Ty), SubtypeClosed (fun tau => tau ∈ S) → ∀ (Gamma : List Source.Ty) (table : Fin n → Fin n → Bool) (source target : List Nat), DirectMultisetPresentation.Direct (QuotientDominationCertificates.relation n arity symbols S Gamma table) source target → listCarrierTest n arity symbols S Gamma source = true → listCarrierTest n arity symbols S Gamma target = true

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCarrierTargets
