module
public import LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCertificatesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCertificatesTargets
open QuotientDirectCertificates

def ActualDirectCertificateSoundness : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Source.Ty) (table : Fin n → Fin n → Bool) (source target : List Nat) (c : Certificate), directTest n arity symbols S Gamma table source target c = true → DirectMultisetPresentation.Direct (QuotientDominationCertificates.relation n arity symbols S Gamma table) source target

def ActualDirectCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Source.Ty) (table : Fin n → Fin n → Bool) (source target : List Nat), (∃ c : Certificate, directTest n arity symbols S Gamma table source target c = true) ↔ DirectMultisetPresentation.Direct (QuotientDominationCertificates.relation n arity symbols S Gamma table) source target

def ActualNumericDirectCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Source.Ty) (table : Fin n → Fin n → Bool) (source target : Nat), (∃ c : Nat, numericTest n arity symbols S Gamma table source target c = true) ↔ ∃ ss ts : List Nat, Encodable.decode source = some ss ∧ Encodable.decode target = some ts ∧ DirectMultisetPresentation.Direct (QuotientDominationCertificates.relation n arity symbols S Gamma table) ss ts

end LogicLineages.OrdinalComparison.TerminationOrdering.QuotientDirectCertificatesTargets
