module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.LayerNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedAuxiliaryCoding NumberedLeastCodeRepresentative
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open OriginalRawSyntaxTransportEvaluationSupportProof InternalApplicationCertificateConstructorsEvaluationProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open Continuation20261114 Continuation20261115
open KeyProof SourceProof RecombinationProof LayerNativeProof

theorem extractValue (n key param : Nat) :
    evaluate (extract n) (ofFn ![key,param]) = value n key param := by
  exact ExchangeSelectedRecursor.NativeProof.nativeFinalValue rank dependency (layer n)
    (fun key _ => (Nat.unpair key).1) (fun key _ => keys key)
    (fun key answers param => recombination n key param answers) (value n)
    rankValue dependencyValue (fun key answers param => layerValue n key param answers)
    (fun key _ child hc => rankDecrease key child hc)
    (recursiveLaw n) key param

theorem fieldsValue (n raw b S H labels tupleBound : Nat) :
    evaluate (fields n) (ofFn ![raw,b,S,H,labels,tupleBound]) =
      value n (Nat.pair raw b) (Nat.pair S (Nat.pair H (Nat.pair labels tupleBound))) := by
  simp [fields,binaryCompositionEvaluation,pairOfEvaluation,projectionEvaluation]
  exact extractValue n (Nat.pair raw b) (Nat.pair S (Nat.pair H (Nat.pair labels tupleBound)))

theorem inputSix (v : List.Vector Nat 6) : v = ofFn ![v.get 0,v.get 1,v.get 2,v.get 3,v.get 4,v.get 5] := by
  apply List.Vector.ext
  intro i
  fin_cases i <;> rfl

theorem nativeBoolean : Targets.NativeBoolean := by
  intro n v
  rw [inputSix v,fieldsValue]
  exact valueBoolean _ _ _

theorem nativeMalformed : Targets.NativeMalformed := by
  intro n v hc
  rw [inputSix v,fieldsValue]
  simp only [value,Nat.unpair_pair,hc,Option.map_none,Option.getD_none]

theorem typedTypes (S : List Source.Ty) (H labels tupleBound : Nat) :
    rawTypes (Nat.pair (Encodable.encode S) (Nat.pair H (Nat.pair labels tupleBound))) = S.map typeNumber := by
  rw [OriginalContextInsertionCalibrationProof.contextNumbers]
  simp only [rawTypes,Nat.unpair_pair,numbersRoundTrip,Option.getD_some]

theorem typedHeads (n : Nat) (S : Nat) (H : List (HeadCode (Fin n))) (labels tupleBound : Nat) :
    rawHeads n (Nat.pair S (Nat.pair (Encodable.encode H) (Nat.pair labels tupleBound))) = H.map headNumber := by
  simp [rawHeads,OriginalTypeListsEnumeration.CodecProof.listEncoding,Nat.unpair_pair,
    numbersRoundTrip,List.map_map,Function.comp_def]

theorem nativeOriginal : Targets.NativeOriginal := by
  intro n S H labels tupleBound b c
  rw [fieldsValue,valueImage,typedTypes,typedHeads]
  simp only [rawLabels,rawTupleBound,Nat.unpair_pair]
  have h := originalFields S H labels tupleBound b c
  simpa using h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.NativeProof
