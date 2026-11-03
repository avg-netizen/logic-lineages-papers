module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedCodeView

private def left (value : Nat) : Nat := (Nat.unpair value).1
private def right (value : Nat) : Nat := (Nat.unpair value).2
private def typeValue (value : Nat) : Ty := (decodeType value).getD .ground
private def typesValue (value : Nat) : List Ty := (decodeTypes value).getD []
private def headValue (n value : Nat) : HeadCode (Fin n) :=
  (decodeHeadNumber n value).getD .zero
private def codeValue (n value : Nat) : Code (Fin n) :=
  (decodeCode n value).getD .argumentsNil

private theorem leftPrimitive : Primrec left := Primrec.fst.comp Primrec.unpair
private theorem rightPrimitive : Primrec right := Primrec.snd.comp Primrec.unpair
private theorem typeValuePrimitive : Primrec typeValue :=
  Primrec.option_getD.comp NumberedTypeCodecPrimrecProof.typeDecoderPrimitive
    (Primrec.const Ty.ground)
private theorem typesValuePrimitive : Primrec typesValue :=
  Primrec.option_getD.comp NumberedTypeCodecPrimrecProof.typeListDecoderPrimitive
    (Primrec.const [])
private theorem headValuePrimitive (n : Nat) : Primrec (headValue n) :=
  Primrec.option_getD.comp (NumberedHeadCodecPrimrecProof.headDecoderPrimitive n)
    (Primrec.const HeadCode.zero)
private theorem codeValuePrimitive (n : Nat) : Primrec (codeValue n) :=
  Primrec.option_getD.comp (NumberedCodeCodecPrimrecProof.codeDecoderPrimitive n)
    (Primrec.const Code.argumentsNil)

private def lamPayload (n value : Nat) : CodeView n :=
  .inr (.inl (typeValue (left value), codeValue n (right value)))

private def appPayload (n value : Nat) : CodeView n :=
  .inr (.inr (.inl (typeValue (left value),
    codeValue n (left (right value)), codeValue n (right (right value)))))

private def bottomPayload (n value : Nat) : CodeView n :=
  .inr (.inr (.inr (.inl (typeValue value))))

private def ordinaryPayload (n value : Nat) : CodeView n :=
  .inr (.inr (.inr (.inr (.inl
    (headValue n (left value), codeValue n (right value))))))

private def numberedPayload (n value : Nat) : CodeView n :=
  .inr (.inr (.inr (.inr (.inr (.inl
    (left value,
     headValue n (left (right value)),
     typeValue (left (right (right value))),
     codeValue n (left (right (right (right value)))),
     typesValue (left (right (right (right (right value))))),
     codeValue n (right (right (right (right (right value)))))))))))

private def argumentsPayload (n value : Nat) : CodeView n :=
  .inr (.inr (.inr (.inr (.inr (.inr (.inr
    (typeValue (left value), codeValue n (left (right value)),
      codeValue n (right (right value)))))))))

private def pairView (n : Nat) (p : Nat × Nat) : CodeView n :=
  if p.1 = 0 then .inl p.2
  else if p.1 = 1 then lamPayload n p.2
  else if p.1 = 2 then appPayload n p.2
  else if p.1 = 3 then bottomPayload n p.2
  else if p.1 = 4 then ordinaryPayload n p.2
  else if p.1 = 5 then numberedPayload n p.2
  else if p.1 = 6 then .inr (.inr (.inr (.inr (.inr (.inr (.inl ()))))))
  else if p.1 = 7 then argumentsPayload n p.2
  else .inl 0

private def numericView (n value : Nat) : CodeView n := pairView n (Nat.unpair value)

private theorem lamPayloadPrimitive (n : Nat) : Primrec (lamPayload n) :=
  Primrec.sumInr.comp (Primrec.sumInl.comp
    ((typeValuePrimitive.comp leftPrimitive).pair
      ((codeValuePrimitive n).comp rightPrimitive)))

private theorem appPayloadPrimitive (n : Nat) : Primrec (appPayload n) :=
  Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.sumInl.comp
    ((typeValuePrimitive.comp leftPrimitive).pair
      (((codeValuePrimitive n).comp (leftPrimitive.comp rightPrimitive)).pair
        ((codeValuePrimitive n).comp (rightPrimitive.comp rightPrimitive))))))

private theorem bottomPayloadPrimitive (n : Nat) : Primrec (bottomPayload n) :=
  Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.sumInr.comp
    (Primrec.sumInl.comp typeValuePrimitive)))

private theorem ordinaryPayloadPrimitive (n : Nat) : Primrec (ordinaryPayload n) :=
  Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.sumInr.comp
    (Primrec.sumInr.comp (Primrec.sumInl.comp
      (((headValuePrimitive n).comp leftPrimitive).pair
        ((codeValuePrimitive n).comp rightPrimitive))))))

private theorem numberedPayloadPrimitive (n : Nat) : Primrec (numberedPayload n) := by
  have h2 : Primrec (fun value => right (right value)) :=
    rightPrimitive.comp rightPrimitive
  have h3 : Primrec (fun value => right (right (right value))) :=
    rightPrimitive.comp h2
  have h4 : Primrec (fun value => right (right (right (right value)))) :=
    rightPrimitive.comp h3
  have h5 : Primrec (fun value => right (right (right (right (right value))))) :=
    rightPrimitive.comp h4
  have fields : Primrec (fun value =>
      (left value,
       headValue n (left (right value)),
       typeValue (left (right (right value))),
       codeValue n (left (right (right (right value)))),
       typesValue (left (right (right (right (right value))))),
       codeValue n (right (right (right (right (right value))))))) :=
    leftPrimitive.pair
      (((headValuePrimitive n).comp (leftPrimitive.comp rightPrimitive)).pair
        ((typeValuePrimitive.comp (leftPrimitive.comp h2)).pair
          (((codeValuePrimitive n).comp (leftPrimitive.comp h3)).pair
            ((typesValuePrimitive.comp (leftPrimitive.comp h4)).pair
              ((codeValuePrimitive n).comp h5)))))
  exact Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.sumInr.comp
    (Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.sumInl.comp fields)))))

private theorem argumentsPayloadPrimitive (n : Nat) : Primrec (argumentsPayload n) :=
  Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.sumInr.comp
    (Primrec.sumInr.comp (Primrec.sumInr.comp (Primrec.sumInr.comp
      (Primrec.sumInr.comp
        ((typeValuePrimitive.comp leftPrimitive).pair
          (((codeValuePrimitive n).comp (leftPrimitive.comp rightPrimitive)).pair
            ((codeValuePrimitive n).comp (rightPrimitive.comp rightPrimitive))))))))))

private theorem pairViewPrimitive (n : Nat) : Primrec (pairView n) :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.sumInl.comp Primrec.snd)
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 1))
      ((lamPayloadPrimitive n).comp Primrec.snd)
      (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 2))
        ((appPayloadPrimitive n).comp Primrec.snd)
        (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 3))
          ((bottomPayloadPrimitive n).comp Primrec.snd)
          (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 4))
            ((ordinaryPayloadPrimitive n).comp Primrec.snd)
            (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 5))
              ((numberedPayloadPrimitive n).comp Primrec.snd)
              (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 6))
                (Primrec.const (view (Code.argumentsNil : Code (Fin n))))
                (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 7))
                  ((argumentsPayloadPrimitive n).comp Primrec.snd)
                  (Primrec.const (Sum.inl 0)))))))))

private theorem numericViewPrimitive (n : Nat) : Primrec (numericView n) :=
  (pairViewPrimitive n).comp Primrec.unpair

private theorem numericViewCalibration (n : Nat) (code : Code (Fin n)) :
    numericView n (codeNumber code) = view code := by
  cases code <;>
    simp [numericView, pairView, lamPayload, appPayload, bottomPayload,
      ordinaryPayload, numberedPayload, argumentsPayload, left, right,
      typeValue, typesValue, headValue, codeValue, codeNumber, view,
      NumberedNumericDecodingSupportProof.typeRoundTrip,
      NumberedNumericDecodingSupportProof.typesRoundTrip,
      NumberedNumericDecodingSupportProof.headNumericRoundTrip,
      NumberedNumericDecodingProof.codeRoundTrip]

theorem viewRoundTrip : NumberedCodeViewTargets.ActualViewRoundTrip := by
  intro n
  constructor
  · intro code
    cases code <;> rfl
  · intro data
    rcases data with index | ⟨sigma, body⟩ | ⟨sigma, q, a⟩ | tau |
      ⟨head, base⟩ | ⟨k, head, tau, base, types, extras⟩ | unit | ⟨tau, q, rest⟩
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · cases unit
      rfl
    · rfl

theorem viewPrimitive : NumberedCodeViewTargets.ActualViewPrimitive := by
  intro n
  exact ((numericViewPrimitive n).comp
    (NumberedCodeCodecPrimrecProof.codeEncoderPrimitive n)).of_eq
      (numericViewCalibration n)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedCodeViewProof
