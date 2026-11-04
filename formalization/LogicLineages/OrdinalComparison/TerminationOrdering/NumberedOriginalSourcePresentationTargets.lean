module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationDefinitions

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationTargets
open Source NumberedOriginalSourceCodec NumberedOriginalSourcePresentation

def ActualPackedRoundTrip : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (p : PackedSource (Fin n) arity Gamma),
  decodePackedSourceNumber n arity Gamma (packedSourceNumber p)=some p

def ActualPackedSound : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (value : Nat) (p : PackedSource (Fin n) arity Gamma),
  decodePackedSourceNumber n arity Gamma value=some p → packedSourceNumber p=value

def ActualFixedValidity : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (tau : Ty) (value : Nat),
  sourceTest n arity Gamma tau value=(decodeSourceNumber n arity Gamma tau value).isSome

def ActualPackedValidity : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty)
    (value : Nat),
  packedSourceTest n arity Gamma value=(decodePackedSourceNumber n arity Gamma value).isSome

def ActualFixedValidityPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : (List Ty × Ty) × Nat => (decodeSourceNumber n arity p.1.1 p.1.2 p.2).isSome)

def ActualPackedValidityPrimitive : Prop := ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : List Ty × Nat => (decodePackedSourceNumber n arity p.1 p.2).isSome)

def ActualFixedPresentation : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty),
  ∃ I : Primcodable (Term (Fin n) arity Gamma tau),
    (∀ s, @Encodable.encode _ I.toEncodable s=sourceNumber s) ∧
    (∀ value, @Encodable.decode _ I.toEncodable value=decodeSourceNumber n arity Gamma tau value)

def ActualPackedPresentation : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty),
  ∃ I : Primcodable (PackedSource (Fin n) arity Gamma),
    (∀ p, @Encodable.encode _ I.toEncodable p=packedSourceNumber p) ∧
    (∀ value, @Encodable.decode _ I.toEncodable value=decodePackedSourceNumber n arity Gamma value)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationTargets
