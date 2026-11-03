module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesTargets
open Source NumberedCopyCertificate NumberedMultisetNumeric NumberedQuotientPaths NumberedNumericQuotientEdge NumberedQuotientPathCertificates

def ActualCountedPathCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (count x y : Nat),
  (∃ entries,entries.length=count ∧ pathTest n arity symbols S Gamma table x y entries=true) ↔
    CountedPath (QuotientEdge n arity symbols S (tableAbove table) Gamma) count x y

def ActualPositivePathCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (x y : Nat),
  (∃ entries,entries≠[] ∧ pathTest n arity symbols S Gamma table x y entries=true) ↔
    PositivePath (QuotientEdge n arity symbols S (tableAbove table) Gamma) x y

def ActualNumericPositivePathCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (x y : Nat),
  (∃ certificate,positivePathTest n arity symbols S Gamma table x y certificate=true) ↔
    PositivePath (QuotientEdge n arity symbols S (tableAbove table) Gamma) x y

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathCertificatesTargets
