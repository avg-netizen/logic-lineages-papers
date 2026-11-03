module
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniverseNumericValidationProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof
open Source NumberedRewriteReduction NumberedAuxiliaryCoding NumberedAuxiliaryDecoding
open NumberedLeastCodeRepresentative NumberedNumericDecoding NumberedNumericCarrier
open NumberedTypedRequests NumberedRequestPresentation NumberedRequestWeight
open NumberedUniverseNumericValidation

private abbrev Window (n : Nat) := List (Fin n) × List Ty
private abbrev TermInput (n : Nat) := Window n × (List Ty × Ty × Code (Fin n))
private abbrev ArgumentsInput (n : Nat) := Window n × (List Ty × List Ty × Code (Fin n))
private abbrev NumericTermInput (n : Nat) := Window n × List Ty × Ty × Nat
private abbrev CarrierInput (n : Nat) := Window n × List Ty × Nat

private theorem termFuelCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (tau : Ty) (code : Code (Fin n)) :
    NumberedUniverseEvaluation.evaluate arity symbols S (codeNumber code + 1)
      [.term Gamma tau code] = (decodeTerm arity Gamma tau code).any (universeTest symbols S) := by
  have hb : workWeight [.term Gamma tau code] ≤ codeNumber code + 1 := by
    simpa [workWeight, requestWeight] using NumberedRequestNumericBoundProof.codeWeightBound n code
  simpa [NumberedUniverseRequests.valid] using
    NumberedUniverseEvaluationProof.sufficientFuelExact n arity symbols S
      (codeNumber code + 1) [.term Gamma tau code] hb

private theorem argumentsFuelCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma types : List Ty) (code : Code (Fin n)) :
    NumberedUniverseEvaluation.evaluate arity symbols S (codeNumber code + 1)
      [.arguments Gamma types code] =
      (decodeArguments arity Gamma types code).any (argumentsUniverseTest symbols S) := by
  have hb : workWeight [.arguments Gamma types code] ≤ codeNumber code + 1 := by
    simpa [workWeight, requestWeight] using NumberedRequestNumericBoundProof.codeWeightBound n code
  simpa [NumberedUniverseRequests.valid] using
    NumberedUniverseEvaluationProof.sufficientFuelExact n arity symbols S
      (codeNumber code + 1) [.arguments Gamma types code] hb

theorem termUniverseSuccessPrimitive : NumberedUniversePrimrecTargets.ActualTermUniverseSuccessPrimitive := by
  intro n arity
  have hfuel : Primrec (fun p : TermInput n => codeNumber p.2.2.2 + 1) :=
    (NumberedRequestNumericBoundProof.codeFuelPrimitive n).comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hrequests : Primrec (fun p : TermInput n => [Request.term p.2.1 p.2.2.1 p.2.2.2]) :=
    Primrec.list_cons.comp ((termRequestPrimitive n).comp Primrec.snd) (Primrec.const [])
  have hinput : Primrec (fun p : TermInput n =>
      (p.1, codeNumber p.2.2.2 + 1, [Request.term p.2.1 p.2.2.1 p.2.2.2])) :=
    Primrec.fst.pair (hfuel.pair hrequests)
  exact ((NumberedUniverseEvaluationProof.evaluatorPrimitive n arity).comp hinput).of_eq
    (fun p => termFuelCalibration n arity p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

theorem argumentsUniverseSuccessPrimitive : NumberedUniversePrimrecTargets.ActualArgumentsUniverseSuccessPrimitive := by
  intro n arity
  have hfuel : Primrec (fun p : ArgumentsInput n => codeNumber p.2.2.2 + 1) :=
    (NumberedRequestNumericBoundProof.codeFuelPrimitive n).comp
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hrequests : Primrec (fun p : ArgumentsInput n =>
      [Request.arguments p.2.1 p.2.2.1 p.2.2.2]) :=
    Primrec.list_cons.comp ((argumentsRequestPrimitive n).comp Primrec.snd) (Primrec.const [])
  have hinput : Primrec (fun p : ArgumentsInput n =>
      (p.1, codeNumber p.2.2.2 + 1, [Request.arguments p.2.1 p.2.2.1 p.2.2.2])) :=
    Primrec.fst.pair (hfuel.pair hrequests)
  exact ((NumberedUniverseEvaluationProof.evaluatorPrimitive n arity).comp hinput).of_eq
    (fun p => argumentsFuelCalibration n arity p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2)

private theorem numericTermValidatorPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : NumericTermInput n => termValid n arity p.1.1 p.1.2 p.2.1 p.2.2.1 p.2.2.2) := by
  have hinput : Primrec (fun p : NumericTermInput n × Code (Fin n) =>
      (p.1.1, p.1.2.1, p.1.2.2.1, p.2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair
        ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))).pair Primrec.snd))
  have hbody : Primrec (fun p : NumericTermInput n × Code (Fin n) =>
      (decodeTerm arity p.1.2.1 p.1.2.2.1 p.2).any (universeTest p.1.1.1 p.1.1.2)) :=
    (termUniverseSuccessPrimitive n arity).comp
      (g := fun p : NumericTermInput n × Code (Fin n) =>
        (p.1.1, p.1.2.1, p.1.2.2.1, p.2)) hinput
  have h : Primrec (fun p : NumericTermInput n =>
      (Option.casesOn (decodeCode n p.2.2.2) false
        (fun code => (decodeTerm arity p.2.1 p.2.2.1 code).any
          (universeTest p.1.1 p.1.2)) : Bool)) :=
    Primrec.option_casesOn
      (o := fun p : NumericTermInput n => decodeCode n p.2.2.2)
      (f := fun _ : NumericTermInput n => false)
      (g := fun p code => (decodeTerm arity p.2.1 p.2.2.1 code).any (universeTest p.1.1 p.1.2))
      ((NumberedCodeCodecPrimrecProof.codeDecoderPrimitive n).comp
        (g := fun p : NumericTermInput n => p.2.2.2)
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const false) hbody.to₂
  apply h.of_eq
  intro p
  rw [NumberedUniverseNumericValidationProof.termValidation]
  cases decodeCode n p.2.2.2 <;> rfl

private theorem packedValidatorCalibration (n : Nat) (arity : Fin n → Nat) (p : CarrierInput n) :
    (Option.casesOn (decodeType (Nat.unpair p.2.2).1) false
      (fun tau => termValid n arity p.1.1 p.1.2 p.2.1 tau (Nat.unpair p.2.2).2) : Bool) =
      packedValid n arity p.1.1 p.1.2 p.2.1 p.2.2 := by
  cases h : decodeType (Nat.unpair p.2.2).1 <;> simp only [packedValid, h, Option.any_none, Option.any_some]

private theorem numericPackedValidatorPrimitive (n : Nat) (arity : Fin n → Nat) :
    Primrec (fun p : CarrierInput n => packedValid n arity p.1.1 p.1.2 p.2.1 p.2.2) := by
  have hnumber : Primrec (fun p : CarrierInput n × Ty => (Nat.unpair p.1.2.2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst)))
  have hinput : Primrec (fun p : CarrierInput n × Ty =>
      (p.1.1, p.1.2.1, p.2, (Nat.unpair p.1.2.2).2)) :=
    (Primrec.fst.comp Primrec.fst).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.fst)).pair (Primrec.snd.pair hnumber))
  have hbody : Primrec (fun p : CarrierInput n × Ty =>
      termValid n arity p.1.1.1 p.1.1.2 p.1.2.1 p.2 (Nat.unpair p.1.2.2).2) :=
    (numericTermValidatorPrimitive n arity).comp
      (g := fun p : CarrierInput n × Ty => (p.1.1, p.1.2.1, p.2, (Nat.unpair p.1.2.2).2)) hinput
  have htype : Primrec (fun p : CarrierInput n => decodeType (Nat.unpair p.2.2).1) :=
    NumberedTypeCodecPrimrecProof.typeDecoderPrimitive.comp
      (g := fun p : CarrierInput n => (Nat.unpair p.2.2).1)
      (Primrec.fst.comp (Primrec.unpair.comp (Primrec.snd.comp Primrec.snd)))
  have h : Primrec (fun p : CarrierInput n =>
      (Option.casesOn (decodeType (Nat.unpair p.2.2).1) false
        (fun tau => termValid n arity p.1.1 p.1.2 p.2.1 tau (Nat.unpair p.2.2).2) : Bool)) :=
    Primrec.option_casesOn
      (o := fun p : CarrierInput n => decodeType (Nat.unpair p.2.2).1)
      (f := fun _ : CarrierInput n => false)
      (g := fun p tau => termValid n arity p.1.1 p.1.2 p.2.1 tau (Nat.unpair p.2.2).2)
      htype (Primrec.const false) hbody.to₂
  exact h.of_eq (packedValidatorCalibration n arity)

theorem rawCarrierPrimitive : NumberedUniversePrimrecTargets.ActualRawCarrierPrimitive := by
  intro n arity
  exact (numericPackedValidatorPrimitive n arity).of_eq
    (fun p => NumberedUniverseNumericValidationProof.rawCarrierValidation n arity p.1.1 p.1.2 p.2.1 p.2.2)

private theorem packedCarrierCalibration (n : Nat) (arity : Fin n → Nat)
    (symbols : List (Fin n)) (S Gamma : List Ty) (q : Packed (Fin n) arity Gamma) :
    rawCarrierTest n arity symbols S Gamma (packedNumber q) = universeTest symbols S q.2 := by
  unfold rawCarrierTest decodeUniverse
  rw [NumberedNumericDecodingProof.packedNumericRoundTrip]
  cases h : universeTest symbols S q.2 <;> simp [h]

theorem packedUniversePrimitive : NumberedUniversePrimrecTargets.ActualPackedUniversePrimitive := by
  intro n arity Gamma
  have hinput : Primrec (fun p : Window n × Packed (Fin n) arity Gamma =>
      (p.1, Gamma, packedNumber p.2)) :=
    Primrec.fst.pair ((Primrec.const Gamma).pair
      ((NumberedPackedCodecPrimrecProof.packedEncoderPrimitive n arity Gamma).comp Primrec.snd))
  exact ((rawCarrierPrimitive n arity).comp hinput).of_eq
    (fun p => packedCarrierCalibration n arity p.1.1 p.1.2 Gamma p.2)

theorem universeDecoderPrimitive : NumberedUniversePrimrecTargets.ActualUniverseDecoderPrimitive := by
  intro n arity Gamma
  have hpredicate : Primrec (fun p : (Window n × Nat) × Packed (Fin n) arity Gamma =>
      universeTest p.1.1.1 p.1.1.2 p.2.2) :=
    (packedUniversePrimitive n arity Gamma).comp
      (g := fun p : (Window n × Nat) × Packed (Fin n) arity Gamma => (p.1.1, p.2))
      ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)
  have hbody : Primrec (fun p : (Window n × Nat) × Packed (Fin n) arity Gamma =>
      bif universeTest p.1.1.1 p.1.1.2 p.2.2 then some p.2 else none) :=
    Primrec.cond hpredicate (Primrec.option_some.comp Primrec.snd) (Primrec.const none)
  have h := Primrec.option_bind
    ((NumberedPackedCodecPrimrecProof.packedDecoderPrimitive n arity Gamma).comp
      (g := fun p : Window n × Nat => p.2) Primrec.snd) hbody.to₂
  apply h.of_eq
  intro p
  cases hd : decodePackedNumber n arity Gamma p.2 with
  | none => simp [decodeUniverse, hd]
  | some q =>
    cases hu : universeTest p.1.1 p.1.2 q.2 <;> simp [decodeUniverse, hd, Option.filter, hu]

end LogicLineages.OrdinalComparison.TerminationOrdering.NumberedUniversePrimrecProof
