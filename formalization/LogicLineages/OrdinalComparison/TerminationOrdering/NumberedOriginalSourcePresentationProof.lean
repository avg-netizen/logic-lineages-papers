module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourceValidityPrimrecProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationProof
open Source NumberedOriginalSourceCodec NumberedOriginalSourcePresentation
open NumberedOriginalSourcePresentationSupportProof NumberedOriginalSourceValidityPrimrecProof

@[reducible] def fixedEncodable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) :
    Encodable (Term (Fin n) arity Gamma tau) where
  encode := sourceNumber
  decode := decodeSourceNumber n arity Gamma tau
  encodek := NumberedOriginalSourceCodecProof.numericRoundTrip n arity Gamma tau

@[reducible] def sourcePackedEncodable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Encodable (PackedSource (Fin n) arity Gamma) where
  encode := packedSourceNumber
  decode := decodePackedSourceNumber n arity Gamma
  encodek := packedRoundTrip n arity Gamma

theorem fixedNormalization (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) (value : Nat) :
    (letI := fixedEncodable n arity Gamma tau
     Encodable.encode (decodeSourceNumber n arity Gamma tau value)) =
      (bif (decodeSourceNumber n arity Gamma tau value).isSome then value+1 else 0) := by
  letI := fixedEncodable n arity Gamma tau
  cases h : decodeSourceNumber n arity Gamma tau value with
  | none => simp [h]
  | some s =>
    have hs := NumberedOriginalSourceCodecProof.numericSound n arity Gamma tau value s h
    change sourceNumber s+1=value+1
    exact congrArg (fun v => v+1) hs

theorem packedNormalization (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (value : Nat) :
    (letI := sourcePackedEncodable n arity Gamma
     Encodable.encode (decodePackedSourceNumber n arity Gamma value)) =
      (bif (decodePackedSourceNumber n arity Gamma value).isSome then value+1 else 0) := by
  letI := sourcePackedEncodable n arity Gamma
  cases h : decodePackedSourceNumber n arity Gamma value with
  | none => simp [h]
  | some p =>
    have hs := packedSound n arity Gamma value p h
    change packedSourceNumber p+1=value+1
    exact congrArg (fun v => v+1) hs

theorem fixedPresentationPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) :
    letI := fixedEncodable n arity Gamma tau
    Nat.Primrec (fun value => Encodable.encode (decodeSourceNumber n arity Gamma tau value)) := by
  have hs : Primrec (fun value => (decodeSourceNumber n arity Gamma tau value).isSome) :=
    (fixedValidityPrimitive n arity).comp ((Primrec.const (Gamma,tau)).pair Primrec.id)
  have h : Primrec (fun value => bif (decodeSourceNumber n arity Gamma tau value).isSome then value+1 else 0) :=
    Primrec.cond hs Primrec.succ (Primrec.const 0)
  exact Primrec.nat_iff.mp (h.of_eq (fun value => (fixedNormalization n arity Gamma tau value).symm))

theorem packedPresentationPrimitive (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    letI := sourcePackedEncodable n arity Gamma
    Nat.Primrec (fun value => Encodable.encode (decodePackedSourceNumber n arity Gamma value)) := by
  have hs : Primrec (fun value => (decodePackedSourceNumber n arity Gamma value).isSome) :=
    (packedValidityPrimitive n arity).comp ((Primrec.const Gamma).pair Primrec.id)
  have h : Primrec (fun value => bif (decodePackedSourceNumber n arity Gamma value).isSome then value+1 else 0) :=
    Primrec.cond hs Primrec.succ (Primrec.const 0)
  exact Primrec.nat_iff.mp (h.of_eq (fun value => (packedNormalization n arity Gamma value).symm))

instance sourceTermPrimcodable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (tau : Ty) :
    Primcodable (Term (Fin n) arity Gamma tau) where
  toEncodable := fixedEncodable n arity Gamma tau
  prim := fixedPresentationPrimitive n arity Gamma tau

instance sourcePackedPrimcodable (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) :
    Primcodable (PackedSource (Fin n) arity Gamma) where
  toEncodable := sourcePackedEncodable n arity Gamma
  prim := packedPresentationPrimitive n arity Gamma

theorem fixedPresentation : NumberedOriginalSourcePresentationTargets.ActualFixedPresentation := by
  intro n arity Gamma tau
  exact ⟨sourceTermPrimcodable n arity Gamma tau,fun _ => rfl,fun _ => rfl⟩

theorem packedPresentation : NumberedOriginalSourcePresentationTargets.ActualPackedPresentation := by
  intro n arity Gamma
  exact ⟨sourcePackedPrimcodable n arity Gamma,fun _ => rfl,fun _ => rfl⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedOriginalSourcePresentationProof
