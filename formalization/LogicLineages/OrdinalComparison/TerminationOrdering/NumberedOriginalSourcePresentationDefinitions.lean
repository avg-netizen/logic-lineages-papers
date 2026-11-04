module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedValidityPrimrecProof

@[expose] public section
/-! Numeric validity and primitive presentations for the actual original syntax.
The raw mask alone is not a parser: genuine typed auxiliary validity is checked
as well. The source encoder is exactly the previously fixed auxiliary number
of the original translation. No source primitive presentation is presumed.
-/
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentation
open Source NumberedRewriteSyntax NumberedRewriteReduction NumberedNumericDecoding
open NumberedLeastCodeRepresentative NumberedOriginalSourceCodec NumberedOriginalSourceShape

abbrev PackedSource (Symbol : Type) (arity : Symbol → Nat) (Gamma : List Ty) :=
  Sigma (Term Symbol arity Gamma)

def packedSourceNumber {n : Nat} {arity : Fin n → Nat} {Gamma : List Ty}
    (p : PackedSource (Fin n) arity Gamma) : Nat := sourceNumber p.2

def decodePackedSourceNumber (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) :
    Option (PackedSource (Fin n) arity Gamma) := do
  let q ← decodePackedNumber n arity Gamma value
  let s ← project q.2
  pure ⟨q.1,s⟩

def rawSourceShape (n value : Nat) : Bool :=
  match decodeCode n (Nat.unpair value).2 with
  | none => false
  | some code => codeShape code

def packedSourceTest (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) : Bool :=
  (decodePackedNumber n arity Gamma value).isSome && rawSourceShape n value

def sourceTest (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) (value : Nat) : Bool :=
  packedSourceTest n arity Gamma value && decide ((Nat.unpair value).1=typeNumber tau)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentation
