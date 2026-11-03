module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedRootDecompositionProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRoot
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate NumberedMultisetCertificate NumberedMultisetNumeric NumberedMulCertificate NumberedDirectCertificate NumberedSelectCertificate NumberedRootDecomposition

inductive RootSelector (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) where
  | direct (rule : DirectRule)
  | select (types : List Ty) (index : Nat)
  | copy (head : Head (Fin n))
  | mul (certificate : MultisetCertificate n arity Gamma)

def selectorNumber {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty} : RootSelector n arity Gamma → Nat
  | .direct (.put label) => Nat.pair 0 label
  | .direct .abstraction => Nat.pair 1 0
  | .direct .beta => Nat.pair 2 0
  | .direct .bottom => Nat.pair 3 0
  | .select types index => Nat.pair 4 (Nat.pair (typesNumber types) index)
  | .copy head => Nat.pair 5 (headNumber (headCode head))
  | .mul certificate => Nat.pair 6 (certificateNumber certificate)

def decodeSelector (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) : Option (RootSelector n arity Gamma) :=
  match Nat.unpair value with
  | (0,label) => some (.direct (.put label))
  | (1,0) => some (.direct .abstraction)
  | (2,0) => some (.direct .beta)
  | (3,0) => some (.direct .bottom)
  | (4,payload) => (decodeTypes (Nat.unpair payload).1).map (fun types => .select types (Nat.unpair payload).2)
  | (5,payload) => (decodeHeadNumber n payload).map (fun head => .copy (decodeHead head))
  | (6,payload) => (decodeCertificate n arity Gamma payload).map .mul
  | _ => none

def selectorTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (q r : Packed (Fin n) arity Gamma) (selector : RootSelector n arity Gamma) : Bool :=
  letI : DecidableEq (Packed (Fin n) arity Gamma) := NumberedAuxiliaryCodingProof.packedDecidableEq
  match selector with
  | .direct rule => decide (directTarget arity Gamma rule q=some r)
  | .select types index => decide (selectTarget arity Gamma types index q=some r)
  | .copy head => decide (copyTarget arity symbols S table Gamma head q=some r)
  | .mul certificate => mulCertificateTest n arity symbols S Gamma q r certificate

def numericRootTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (source target certificate : Nat) : Bool :=
  match decodeUniverse n arity symbols S Gamma source,decodePackedNumber n arity Gamma target,decodeSelector n arity Gamma certificate with
  | some q,some r,some selector => selectorTest n arity symbols S Gamma table q r selector
  | _,_,_ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericRoot
