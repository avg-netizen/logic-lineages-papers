module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDominationCertificatesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDominationCertificatesTargets
open QuotientDominationCertificates

def ActualOccurrenceSoundness : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Source.Ty) (table : Fin n → Fin n → Bool) (removed inserted : List Nat), ∀ entries : List Entry, test n arity symbols S Gamma table removed inserted entries = true → entries.length = inserted.length ∧ DirectMultisetPresentation.Witnesses (relation n arity symbols S Gamma table) removed inserted (entries.map Prod.fst)

def ActualWitnessCompletion : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Source.Ty) (table : Fin n → Fin n → Bool) (removed inserted : List Nat), ∀ indices : List Nat, DirectMultisetPresentation.Witnesses (relation n arity symbols S Gamma table) removed inserted indices → ∃ entries : List Entry, entries.map Prod.fst = indices ∧ test n arity symbols S Gamma table removed inserted entries = true

def ActualDominationCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Source.Ty) (table : Fin n → Fin n → Bool) (removed inserted : List Nat), (∃ entries : List Entry, test n arity symbols S Gamma table removed inserted entries = true) ↔ ∀ y ∈ inserted, ∃ z ∈ removed, relation n arity symbols S Gamma table z y

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDominationCertificatesTargets
