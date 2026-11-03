module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedValidityPrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedEvaluationPrimrecProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedValidityPrimrecProof
open Source NumberedAuxiliaryCoding NumberedAuxiliaryDecoding NumberedLeastCodeRepresentative
open NumberedNumericDecoding NumberedTypedRequests NumberedRequestWeight NumberedTypedEvaluation
open NumberedRequestPresentation NumberedNumericTypedValidation

private theorem termFuelCalibration (n : Nat) (arity : Fin n → Nat)
    (Gamma : List Ty) (tau : Ty) (code : Code (Fin n)) :
    evaluate arity (codeNumber code + 1) [.term Gamma tau code] =
      (decodeTerm arity Gamma tau code).isSome := by
  have hb : workWeight [.term Gamma tau code] ≤ codeNumber code + 1 := by
    simpa [workWeight, requestWeight] using
      NumberedRequestNumericBoundProof.codeWeightBound n code
  simpa [valid] using NumberedTypedEvaluationProof.sufficientFuelExact
    n arity (codeNumber code + 1) [.term Gamma tau code] hb

private theorem argumentsFuelCalibration (n : Nat) (arity : Fin n → Nat)
    (Gamma types : List Ty) (code : Code (Fin n)) :
    evaluate arity (codeNumber code + 1) [.arguments Gamma types code] =
      (decodeArguments arity Gamma types code).isSome := by
  have hb : workWeight [.arguments Gamma types code] ≤ codeNumber code + 1 := by
    simpa [workWeight, requestWeight] using
      NumberedRequestNumericBoundProof.codeWeightBound n code
  simpa [valid] using NumberedTypedEvaluationProof.sufficientFuelExact
    n arity (codeNumber code + 1) [.arguments Gamma types code] hb

theorem termSuccessPrimitive : NumberedTypedValidityPrimrecTargets.ActualTermSuccessPrimitive := by
  intro n arity
  have hfuel : Primrec (fun p : List Ty × Ty × Code (Fin n) => codeNumber p.2.2 + 1) :=
    (NumberedRequestNumericBoundProof.codeFuelPrimitive n).comp
      (Primrec.snd.comp Primrec.snd)
  have hrequests : Primrec (fun p : List Ty × Ty × Code (Fin n) =>
      [Request.term p.1 p.2.1 p.2.2]) :=
    Primrec.list_cons.comp (termRequestPrimitive n) (Primrec.const [])
  have he := (NumberedTypedEvaluationPrimrecProof.evaluatorPrimitive n arity).comp
    (hfuel.pair hrequests)
  exact he.of_eq (fun p => termFuelCalibration n arity p.1 p.2.1 p.2.2)

theorem argumentsSuccessPrimitive : NumberedTypedValidityPrimrecTargets.ActualArgumentsSuccessPrimitive := by
  intro n arity
  have hfuel : Primrec (fun p : List Ty × List Ty × Code (Fin n) => codeNumber p.2.2 + 1) :=
    (NumberedRequestNumericBoundProof.codeFuelPrimitive n).comp
      (Primrec.snd.comp Primrec.snd)
  have hrequests : Primrec (fun p : List Ty × List Ty × Code (Fin n) =>
      [Request.arguments p.1 p.2.1 p.2.2]) :=
    Primrec.list_cons.comp (argumentsRequestPrimitive n) (Primrec.const [])
  have he := (NumberedTypedEvaluationPrimrecProof.evaluatorPrimitive n arity).comp
    (hfuel.pair hrequests)
  exact he.of_eq (fun p => argumentsFuelCalibration n arity p.1 p.2.1 p.2.2)

theorem numericTermSuccessPrimitive : NumberedTypedValidityPrimrecTargets.ActualNumericTermSuccessPrimitive := by
  intro n arity
  have hbody : Primrec (fun p : (List Ty × Ty × Nat) × Code (Fin n) =>
      (decodeTerm arity p.1.1 p.1.2.1 p.2).isSome) :=
    (termSuccessPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  have h : Primrec (fun p : List Ty × Ty × Nat =>
      (Option.casesOn (decodeCode n p.2.2) false
        (fun code => (decodeTerm arity p.1 p.2.1 code).isSome) : Bool)) :=
    Primrec.option_casesOn
      ((NumberedCodeCodecPrimrecProof.codeDecoderPrimitive n).comp
        (Primrec.snd.comp Primrec.snd))
      (Primrec.const false) hbody.to₂
  apply h.of_eq
  intro p
  cases decodeCode n p.2.2 <;> rfl

theorem numericArgumentsSuccessPrimitive : NumberedTypedValidityPrimrecTargets.ActualNumericArgumentsSuccessPrimitive := by
  intro n arity
  have hbody : Primrec (fun p : (List Ty × List Ty × Nat) × Code (Fin n) =>
      (decodeArguments arity p.1.1 p.1.2.1 p.2).isSome) :=
    (argumentsSuccessPrimitive n arity).comp
      ((Primrec.fst.comp Primrec.fst).pair
        ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair Primrec.snd))
  have h : Primrec (fun p : List Ty × List Ty × Nat =>
      (Option.casesOn (decodeCode n p.2.2) false
        (fun code => (decodeArguments arity p.1 p.2.1 code).isSome) : Bool)) :=
    Primrec.option_casesOn
      ((NumberedCodeCodecPrimrecProof.codeDecoderPrimitive n).comp
        (Primrec.snd.comp Primrec.snd))
      (Primrec.const false) hbody.to₂
  apply h.of_eq
  intro p
  cases decodeCode n p.2.2 <;> rfl

theorem numericTermValidatorPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : List Ty × Ty × Nat => termValid n arity p.1 p.2.1 p.2.2) :=
  (numericTermSuccessPrimitive n arity).of_eq
    (fun p => (NumberedNumericTypedValidationProof.termValidation n arity p.1 p.2.1 p.2.2).symm)

private theorem packedValidatorCalibration (n : Nat) (arity : Fin n → Nat)
    (p : List Ty × Nat) :
    (Option.casesOn (decodeType (Nat.unpair p.2).1) false
      (fun tau => termValid n arity p.1 tau (Nat.unpair p.2).2) : Bool) =
      packedValid n arity p.1 p.2 := by
  cases h : decodeType (Nat.unpair p.2).1 <;> simp only [packedValid, h]

theorem numericPackedValidatorPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : List Ty × Nat => packedValid n arity p.1 p.2) := by
  have hinput : Primrec (fun p : (List Ty × Nat) × Ty =>
      (p.1.1, p.2, (Nat.unpair p.1.2).2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      (Primrec.snd.pair (Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.fst))))
  have hbody : Primrec (fun p : (List Ty × Nat) × Ty =>
      termValid n arity p.1.1 p.2 (Nat.unpair p.1.2).2) :=
    (numericTermValidatorPrimitive n arity).comp
      (g := fun p : (List Ty × Nat) × Ty => (p.1.1, p.2, (Nat.unpair p.1.2).2)) hinput
  have htype : Primrec (fun p : List Ty × Nat =>
      decodeType (Nat.unpair p.2).1) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp
      (g := fun p : List Ty × Nat => (Nat.unpair p.2).1)
      (Primrec.fst.comp (Primrec.unpair.comp Primrec.snd))
  have h : Primrec (fun p : List Ty × Nat =>
      (Option.casesOn (decodeType (Nat.unpair p.2).1) false
        (fun tau => termValid n arity p.1 tau (Nat.unpair p.2).2) : Bool)) :=
    Primrec.option_casesOn
      (o := fun p : List Ty × Nat => decodeType (Nat.unpair p.2).1)
      (f := fun _ : List Ty × Nat => false)
      (g := fun p tau => termValid n arity p.1 tau (Nat.unpair p.2).2)
      htype
      (Primrec.const false) hbody.to₂
  exact h.of_eq (packedValidatorCalibration n arity)

theorem numericPackedSuccessPrimitive : NumberedTypedValidityPrimrecTargets.ActualNumericPackedSuccessPrimitive := by
  intro n arity
  exact (numericPackedValidatorPrimitive n arity).of_eq
    (fun p => NumberedNumericTypedValidationProof.packedValidation n arity p.1 p.2)

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedTypedValidityPrimrecProof
