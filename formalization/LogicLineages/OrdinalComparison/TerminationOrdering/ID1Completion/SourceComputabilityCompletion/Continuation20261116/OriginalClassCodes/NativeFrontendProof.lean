module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeSelectorsProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeFrontendProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open Continuation20261114 Continuation20261115
open NativeMapProof NativeSelectorsProof

theorem headsValue (n : Nat) (arity : Fin n → Nat) (root raw table gam : Nat)
    (syms : List (Fin n)) (S : List Source.Ty) :
    evaluate (heads n arity)
      (input root raw (numbersNumber (syms.map Fin.val)) (numbersNumber (S.map typeNumber)) table gam) =
      Encodable.encode (NumberedAuxiliaryEnumeration.sourceHeads arity syms S) := by
  rw [heads,unaryCompositionEvaluation,binaryCompositionEvaluation,symbolsValue,typesValue,
    OriginalSourceHeads.NativeProof.sourceValue]
  exact encodedHeads n _

theorem nodeValue (n : Nat) (root syms ts table : Nat) (code : Code (Fin n))
    (Gamma : List Source.Ty) :
    evaluate (node n) (input root (codeNumber code) syms ts table (Encodable.encode Gamma)) =
      Encodable.encode (Gamma.length,2*(NumberedSyntaxBoundsPrimrec.codeBounds code).1) := by
  rw [node,pairOfEvaluation,boundValue,fuelValue]
  rfl

theorem parameterValue (n : Nat) (arity : Fin n → Nat) (root table gam : Nat)
    (syms : List (Fin n)) (S : List Source.Ty) (code : Code (Fin n)) :
    evaluate (parameter n arity)
      (input root (codeNumber code) (numbersNumber (syms.map Fin.val))
        (numbersNumber (S.map typeNumber)) table gam) =
      Encodable.encode (S,(NumberedAuxiliaryEnumeration.sourceHeads arity syms S,
        ((NumberedSyntaxBoundsPrimrec.codeBounds code).2,(NumberedSyntaxBoundsPrimrec.codeBounds code).1))) := by
  simp only [parameter,pairOfEvaluation,typesValue,headsValue,labelValue,sizeValue]
  rw [← OriginalContextInsertionCalibrationProof.contextNumbers]
  rfl

theorem enumerationValue (n : Nat) (arity : Fin n → Nat) (root table : Nat)
    (syms : List (Fin n)) (S Gamma : List Source.Ty) (code : Code (Fin n)) :
    evaluate (enumerated n arity)
      (input root (codeNumber code) (numbersNumber (syms.map Fin.val))
        (numbersNumber (S.map typeNumber)) table (Encodable.encode Gamma)) =
      Encodable.encode (NumberedAuxiliaryEnumeration.enumerate S
        (NumberedAuxiliaryEnumeration.sourceHeads arity syms S)
        (NumberedSyntaxBoundsPrimrec.codeBounds code).2 (NumberedSyntaxBoundsPrimrec.codeBounds code).1
        Gamma.length (2*(NumberedSyntaxBoundsPrimrec.codeBounds code).1)) := by
  rw [enumerated,binaryCompositionEvaluation,nodeValue,parameterValue]
  exact OriginalEnumerationRecursion.NativeProof.nativeOriginal n _ _ _

theorem frontendValue (n : Nat) (arity : Fin n → Nat) (table : Nat)
    (syms : List (Fin n)) (S Gamma : List Source.Ty) (q : NumberedUniformPackedDecoding.RawPacked n) :
    evaluate (frontend n arity)
      (input (Encodable.encode q.1) (codeNumber q.2) (numbersNumber (syms.map Fin.val))
        (numbersNumber (S.map typeNumber)) table (Encodable.encode Gamma)) =
      TwoSol20261113.CalibratedPrimary.Membership.entriesCode
        (ContextUniformPrimary.classCodes arity syms S Gamma q) := by
  rw [frontend,binaryCompositionEvaluation,enumerationValue,rootValue,pairRootsOriginal]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeFrontendProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalClassCodes.NativeFrontendProof
