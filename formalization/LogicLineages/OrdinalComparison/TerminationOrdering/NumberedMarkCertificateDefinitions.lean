module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificate
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericCarrier NumberedCopyCertificate

def markTarget {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} (label : Nat)
    (q : Packed (Fin n) arity Gamma) : Option (Packed (Fin n) arity Gamma) :=
  (finiteMark label q.2).map (fun r => ⟨q.1,r⟩)

def markCertificateTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (source target label : Nat) : Bool :=
  match decodeUniverse n arity symbols S Gamma source with
  | some q => match markTarget label q with
    | some r => decide (packedNumber r=target)
    | none => false
  | none => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMarkCertificate
