module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericCarrierProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificate
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier

def tableAbove {n : Nat} (table : Fin n → Fin n → Bool) (f g : Fin n) : Prop := table f g=true
instance tableAboveDecidable {n : Nat} (table : Fin n → Fin n → Bool) : DecidableRel (tableAbove table) := fun f g => inferInstanceAs (Decidable (table f g=true))

inductive CopyInstance (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (table : Fin n → Fin n → Bool) (Gamma : List Ty) (g : Head (Fin n)) : Packed (Fin n) arity Gamma → Packed (Fin n) arity Gamma → Prop where
  | copy (k : Nat) (f : Head (Fin n)) (base : AuxArguments (Fin n) arity Gamma (headArguments arity f))
      (types : List Ty) (extras : AuxArguments (Fin n) arity Gamma types) :
      RecursiveComparison.headAbove (tableAbove table) f g → HeadInWindow arity symbols S g →
      CopyInstance n arity symbols S table Gamma g
        ⟨headResult g,.numbered (k+1) f (headResult g) base types extras⟩
        ⟨headResult g,.ordinary g (selfArguments k f base types extras (headArguments arity g))⟩

def copyTarget {n : Nat} (arity : Fin n → Nat) (symbols : List (Fin n)) (S : List Ty)
    (table : Fin n → Fin n → Bool) (Gamma : List Ty) (g : Head (Fin n)) (q : Packed (Fin n) arity Gamma) : Option (Packed (Fin n) arity Gamma) :=
  match q.2 with
  | .numbered (k+1) f tau base types extras =>
    if tau=headResult g ∧ RecursiveComparison.headAbove (tableAbove table) f g ∧ HeadInWindow arity symbols S g then
      some ⟨headResult g,.ordinary g (selfArguments k f base types extras (headArguments arity g))⟩
    else none
  | _ => none

def copyCertificateTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (source target certificate : Nat) : Bool :=
  match decodeUniverse n arity symbols S Gamma source,decodeHeadNumber n certificate with
  | some q,some g => match copyTarget arity symbols S table Gamma (decodeHead g) q with
    | some r => decide (packedNumber r=target)
    | none => false
  | _,_ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCopyCertificate
