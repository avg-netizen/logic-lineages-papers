module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedQuotientPathsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecoding
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative

def typeParse : Nat → Nat → Option Ty
  | 0,_ => none
  | fuel+1,0 => some .ground
  | fuel+1,value+1 => do
    let sigma ← typeParse fuel (Nat.unpair value).1
    let tau ← typeParse fuel (Nat.unpair value).2
    pure (.arrow sigma tau)

def decodeType (value : Nat) : Option Ty :=
  (typeParse (value+1) value).filter (fun tau => typeNumber tau=value)

def typesParse : Nat → Nat → Option (List Ty)
  | 0,_ => none
  | fuel+1,0 => some []
  | fuel+1,value+1 => do
    let tau ← decodeType (Nat.unpair value).1
    let rest ← typesParse fuel (Nat.unpair value).2
    pure (tau::rest)

def decodeTypes (value : Nat) : Option (List Ty) :=
  (typesParse (value+1) value).filter (fun types => typesNumber types=value)

def headParse (n value : Nat) : Option (HeadCode (Fin n)) :=
  let tag := (Nat.unpair value).1
  let payload := (Nat.unpair value).2
  match tag with
  | 0 => if payload=0 then some .zero else none
  | 1 => if payload=0 then some .succ else none
  | 2 => (decodeType payload).map HeadCode.cases
  | 3 => (decodeType payload).map HeadCode.recursor
  | 4 => do
    let sigma ← decodeType (Nat.unpair payload).1
    let tau ← decodeType (Nat.unpair payload).2
    pure (.application sigma tau)
  | 5 => if h : payload<n then some (.ranked ⟨payload,h⟩) else none
  | _ => none

def decodeHeadNumber (n value : Nat) : Option (HeadCode (Fin n)) :=
  (headParse n value).filter (fun head => headNumber head=value)

def codeParse (n : Nat) : Nat → Nat → Option (Code (Fin n))
  | 0,_ => none
  | fuel+1,value =>
    let tag := (Nat.unpair value).1
    let payload := (Nat.unpair value).2
    match tag with
    | 0 => some (.var payload)
    | 1 => do
      let sigma ← decodeType (Nat.unpair payload).1
      let body ← codeParse n fuel (Nat.unpair payload).2
      pure (.lam sigma body)
    | 2 => do
      let sigma ← decodeType (Nat.unpair payload).1
      let children := (Nat.unpair payload).2
      let q ← codeParse n fuel (Nat.unpair children).1
      let a ← codeParse n fuel (Nat.unpair children).2
      pure (.app sigma q a)
    | 3 => (decodeType payload).map Code.bottom
    | 4 => do
      let head ← decodeHeadNumber n (Nat.unpair payload).1
      let base ← codeParse n fuel (Nat.unpair payload).2
      pure (.ordinary head base)
    | 5 => do
      let k := (Nat.unpair payload).1
      let p1 := (Nat.unpair payload).2
      let head ← decodeHeadNumber n (Nat.unpair p1).1
      let p2 := (Nat.unpair p1).2
      let tau ← decodeType (Nat.unpair p2).1
      let p3 := (Nat.unpair p2).2
      let base ← codeParse n fuel (Nat.unpair p3).1
      let p4 := (Nat.unpair p3).2
      let types ← decodeTypes (Nat.unpair p4).1
      let extras ← codeParse n fuel (Nat.unpair p4).2
      pure (.numbered k head tau base types extras)
    | 6 => if payload=0 then some .argumentsNil else none
    | 7 => do
      let tau ← decodeType (Nat.unpair payload).1
      let children := (Nat.unpair payload).2
      let q ← codeParse n fuel (Nat.unpair children).1
      let rest ← codeParse n fuel (Nat.unpair children).2
      pure (.argumentsCons tau q rest)
    | _ => none

def decodeCode (n value : Nat) : Option (Code (Fin n)) :=
  (codeParse n (value+1) value).filter (fun c => codeNumber c=value)

def packedParse (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) : Option (Packed (Fin n) arity Gamma) := do
  let tau ← decodeType (Nat.unpair value).1
  let code ← decodeCode n (Nat.unpair value).2
  decodePacked arity Gamma (tau,code)

def decodePackedNumber (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) : Option (Packed (Fin n) arity Gamma) :=
  (packedParse n arity Gamma value).filter (fun q => packedNumber q=value)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedNumericDecoding
