module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeAnswerSlots.NativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.EncodedMetadataFields.NativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.NativeProof
open Source NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open OriginalRawSyntaxTransport OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsEvaluationProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalAcceptanceCalibrationProof

theorem encodeNone {A : Type} [Encodable A] : Encodable.encode (none : Option A) = 0 := rfl
theorem encodeSome {A : Type} [Encodable A] (a : A) : Encodable.encode (some a) = Encodable.encode a + 1 := rfl
theorem encodeEntry (n : Nat) (tau : Ty) (q : Code (Fin n)) :
    Encodable.encode (tau,q) = Nat.pair (typeNumber tau) (codeNumber q) := rfl
theorem encodeNil {A : Type} [Encodable A] : Encodable.encode ([] : List A) = 0 := rfl
theorem encodeCons {A : Type} [Encodable A] (a : A) (xs : List A) :
    Encodable.encode (a::xs) = 1 + Nat.pair (Encodable.encode a) (Encodable.encode xs) := by
  change Nat.succ (Nat.pair (Encodable.encode a) (Encodable.encodeList xs)) = _
  rw [Nat.add_comm]
  rfl

theorem typeEncoding (tau : Ty) : Encodable.encode tau = typeNumber tau := rfl
theorem codeEncoding (n : Nat) (c : Code (Fin n)) : Encodable.encode c = codeNumber c := rfl
theorem projectionEvaluation {n : Nat} (i : Fin n) (v : List.Vector Nat n) :
    evaluate (.projection i) v = v.get i := rfl

theorem getOne (x t : Nat) : (x ::ᵥ t ::ᵥ List.Vector.nil).get (1 : Fin 2) = t := rfl

theorem prependValue (x t : Nat) :
    evaluate prepend (List.Vector.ofFn ![x,t]) =
      1 + Nat.pair (Nat.pair (Nat.unpair (Nat.unpair x).2).1
        (Nat.unpair (Nat.unpair (Nat.unpair x).2).2).1) (t-1) := by
  change evaluate (consOf entry tailList) (List.Vector.ofFn ![x,t]) = _
  rw [consOfEvaluation]
  simp only [entry,pairOfEvaluation,annotation,child,leftOfEvaluation,rightOfEvaluation,
    tailList,predecessorCompositionEvaluation]
  rfl

theorem stepValue (x t : Nat) : evaluate step (List.Vector.ofFn ![x,t]) =
    if (Nat.unpair x).1 = 6 then 1 else
    if (Nat.unpair x).1 = 7 then
      if t = 0 then 0 else
        (1 + Nat.pair (Nat.pair (Nat.unpair (Nat.unpair x).2).1
          (Nat.unpair (Nat.unpair (Nat.unpair x).2).2).1) (t-1)) + 1
    else 0 := by
  simp only [step,choose,consCase,evalBranch,sameOfEvaluation,leftOfEvaluation,
    constantEvaluation,succOfEvaluation,prependValue]
  change (if (if (Nat.unpair x).1 = 6 then 1 else 0) = 0 then _ else _) = _
  by_cases h6 : (Nat.unpair x).1 = 6 <;> by_cases h7 : (Nat.unpair x).1 = 7 <;>
    by_cases ht : t = 0 <;> simp [h6,h7,ht,raw,tailOption,projectionEvaluation,getOne]

theorem nativeStep (n : Nat) (c : Code (Fin n))
    (tail : Option (List (Ty × Code (Fin n)))) :
    evaluate step (List.Vector.ofFn ![codeNumber c,Encodable.encode tail]) =
      Encodable.encode (semanticStep c tail) := by
  rw [stepValue]
  cases c <;> cases tail <;>
    simp [codeNumber,Nat.unpair_pair,semanticStep,encodeNone,encodeSome,encodeNil,
      encodeCons,encodeEntry,typeEncoding,codeEncoding,Nat.add_comm]

theorem encodedGet (n k : Nat) (answers : List (Option (List (Ty × Code (Fin n))))) :
    (answers.map Encodable.encode).getD k 0 = Encodable.encode (answers.getD k none) := by
  induction answers generalizing k with
  | nil => rfl
  | cons a rest ih =>
    cases k with
    | zero => rfl
    | succ k => exact ih k

theorem nativeRecombine (n : Nat) (c : Code (Fin n))
    (answers : List (Option (List (Ty × Code (Fin n))))) :
    evaluate recombine (List.Vector.ofFn ![codeNumber c,
      NumberedMultisetNumeric.numbersNumber (answers.map Encodable.encode)]) =
      Encodable.encode (some (semanticStep c (answers.getD 1 none))) := by
  rw [recombine,succOfEvaluation,binaryCompositionEvaluation]
  have ht : evaluate tailAnswer (List.Vector.ofFn ![codeNumber c,
      NumberedMultisetNumeric.numbersNumber (answers.map Encodable.encode)]) =
      Encodable.encode (answers.getD 1 none) := by
    rw [tailAnswer,binaryCompositionEvaluation,constantEvaluation]
    change evaluate InternalRawListRecursion.lookup
      (1 ::ᵥ NumberedMultisetNumeric.numbersNumber (answers.map Encodable.encode) ::ᵥ List.Vector.nil) = _
    rw [ExchangeAnswerSlots.NativeProof.lookupEncoded,encodedGet]
  rw [ht]
  change evaluate step (List.Vector.ofFn ![codeNumber c,Encodable.encode (answers.getD 1 none)]) + 1 = _
  rw [nativeStep,encodeSome]

theorem nativeLayer : Targets.NativeLayer := ⟨nativeStep,nativeRecombine⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ArgumentEntriesLayer.NativeProof
