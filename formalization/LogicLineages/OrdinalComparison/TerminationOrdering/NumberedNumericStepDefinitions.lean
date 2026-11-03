module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedStepCertificateProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStep
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedFiniteUniverse NumberedWindowReduction NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier NumberedCopyCertificate NumberedMultisetNumeric NumberedTypedFocus NumberedStepCertificate

def positionNumber : Position → Nat
  | .lam => Nat.pair 0 0
  | .appFunction => Nat.pair 1 0
  | .ordinaryBase index => Nat.pair 2 index
  | .numberedBase index => Nat.pair 3 index
  | .numberedExtras index => Nat.pair 4 index

def decodePosition (value : Nat) : Option Position :=
  match Nat.unpair value with
  | (0,0) => some .lam
  | (1,0) => some .appFunction
  | (2,index) => some (.ordinaryBase index)
  | (3,index) => some (.numberedBase index)
  | (4,index) => some (.numberedExtras index)
  | _ => none

def pathNumber (path : List Position) : Nat := numbersNumber (path.map positionNumber)

def decodePositions : List Nat → Option (List Position)
  | [] => some []
  | value::rest => do
    let position ← decodePosition value
    let path ← decodePositions rest
    pure (position::path)

def decodePath (value : Nat) : Option (List Position) := do
  let values ← decodeNumbers value
  decodePositions values

def stepCertificateNumber (c : StepCertificate) : Nat := Nat.pair (pathNumber c.path) (Nat.pair c.replacement c.root)

def decodeStepCertificate (value : Nat) : Option StepCertificate :=
  (decodePath (Nat.unpair value).1).map (fun path => ⟨path,(Nat.unpair (Nat.unpair value).2).1,(Nat.unpair (Nat.unpair value).2).2⟩)

def numericStepTest (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (table : Fin n → Fin n → Bool) (source target certificate : Nat) : Bool :=
  match decodeUniverse n arity symbols S Gamma source,decodePackedNumber n arity Gamma target,decodeStepCertificate certificate with
  | some ⟨tau,q⟩,some ⟨sigma,r⟩,some c =>
    if ht : sigma=tau then stepTest n arity symbols S Gamma table q (ht ▸ r) c else false
  | _,_,_ => false

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericStep
