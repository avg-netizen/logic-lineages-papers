module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetCertificateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetCertificateTargets
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedMarkCertificate NumberedMultisetCertificate

def ActualReplacementCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (removed inserted : List (Packed (Fin n) arity Gamma)),
  (∃ witnesses,replacementTest removed inserted witnesses=true) ↔
    ∀ q∈inserted,∃ s∈removed,PrimitiveMark (Fin n) arity Gamma s q

def ActualOccurrenceWitnessCount : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (removed inserted : List (Packed (Fin n) arity Gamma)) (witnesses : List MarkWitness),
  replacementTest removed inserted witnesses=true → witnesses.length=inserted.length

def ActualPrimitiveMultisetCertificates : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (source target : List (Packed (Fin n) arity Gamma)),
  (∃ certificate,multisetTest source target certificate=true) ↔ PrimitiveMultiset source target

def ActualMultisetCertificateConfinement : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (source target : List (Packed (Fin n) arity Gamma)) (certificate : MultisetCertificate n arity Gamma),
  multisetTest source target certificate=true → (∀ q∈source,InUniverse symbols S q.2) →
    ∀ q∈target,InUniverse symbols S q.2

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetCertificateTargets
