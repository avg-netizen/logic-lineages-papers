module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportConstructorEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.NativeSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
open OriginalNumberedEnumerationBranch

def pairs (xs ys : List Nat) : List Nat := xs.flatMap (fun a => ys.map (Nat.pair a))
def inputs (a b c d e f : List Nat) : List.Vector Nat 6 :=
  ofFn ![numbersNumber a,numbersNumber b,numbersNumber c,numbersNumber d,numbersNumber e,numbersNumber f]

theorem product56Value (a b c d e f : List Nat) :
    evaluate product56 (inputs a b c d e f) = numbersNumber (pairs e f) := by
  change evaluate NumericDependencyCross.cross (ofFn ![numbersNumber e,numbersNumber f]) = _
  exact NumericDependencyCross.NativeProof.crossValue e f

theorem product456Value (a b c d e f : List Nat) :
    evaluate product456 (inputs a b c d e f) = numbersNumber (pairs d (pairs e f)) := by
  change evaluate NumericDependencyCross.cross (ofFn ![numbersNumber d,evaluate product56 (inputs a b c d e f)]) = _
  rw [product56Value]
  exact NumericDependencyCross.NativeProof.crossValue _ _

theorem product3456Value (a b c d e f : List Nat) :
    evaluate product3456 (inputs a b c d e f) = numbersNumber (pairs c (pairs d (pairs e f))) := by
  change evaluate NumericDependencyCross.cross (ofFn ![numbersNumber c,evaluate product456 (inputs a b c d e f)]) = _
  rw [product456Value]
  exact NumericDependencyCross.NativeProof.crossValue _ _

theorem product23456Value (a b c d e f : List Nat) :
    evaluate product23456 (inputs a b c d e f) = numbersNumber (pairs b (pairs c (pairs d (pairs e f)))) := by
  change evaluate NumericDependencyCross.cross (ofFn ![numbersNumber b,evaluate product3456 (inputs a b c d e f)]) = _
  rw [product3456Value]
  exact NumericDependencyCross.NativeProof.crossValue _ _

theorem productValue (a b c d e f : List Nat) :
    evaluate product123456 (inputs a b c d e f) = numbersNumber (pairs a (pairs b (pairs c (pairs d (pairs e f))))) := by
  change evaluate NumericDependencyCross.cross (ofFn ![numbersNumber a,evaluate product23456 (inputs a b c d e f)]) = _
  rw [product23456Value]
  exact NumericDependencyCross.NativeProof.crossValue _ _

theorem tagValue (v : List.Vector Nat 1) : evaluate tagPayload v = Nat.pair 5 (v.get 0) := by
  simp only [tagPayload,pairOfEvaluation,constantEvaluation,projectionEvaluation]

theorem mapValue (xs : List Nat) :
    evaluate (InternalListMap.map tagPayload) (ofFn ![numbersNumber xs]) = numbersNumber (xs.map (Nat.pair 5)) := by
  have hm := InternalListMapEvaluationProof.actualRawListMapEvaluation 0 tagPayload nil (numbersNumber xs)
  change evaluate (InternalListMap.map tagPayload) (ofFn ![numbersNumber xs]) = _ at hm
  rw [hm,numbersRoundTrip]
  change numbersNumber (xs.map (fun x => evaluate tagPayload (x ::ᵥ nil))) = _
  simp only [tagValue]
  rfl

theorem rawBranchValue (a b c d e f : List Nat) :
    evaluate OriginalNumberedEnumerationBranch.branch (inputs a b c d e f) =
      numbersNumber ((pairs a (pairs b (pairs c (pairs d (pairs e f))))).map (Nat.pair 5)) := by
  change evaluate (InternalListMap.map tagPayload) (ofFn ![evaluate product123456 (inputs a b c d e f)]) = _
  rw [productValue,mapValue]

theorem convertedValue (n : Nat) (heads : List Nat) :
    evaluate (convertedHeads n) (ofFn ![numbersNumber heads]) =
      numbersNumber (heads.map (fun h => evaluate (OriginalEncodedHeadConversion.convert n) (ofFn ![h]))) := by
  have hm := InternalListMapEvaluationProof.actualRawListMapEvaluation 0
    (OriginalEncodedHeadConversion.convert n) nil (numbersNumber heads)
  change evaluate (convertedHeads n) (ofFn ![numbersNumber heads]) = _ at hm
  rw [hm,numbersRoundTrip]
  rfl

theorem branchValue (n : Nat) (a b c d e f : List Nat) :
    evaluate (OriginalEncodedNumberedEnumerationBranch.branch n) (inputs a b c d e f) =
      numbersNumber ((pairs a (pairs (b.map (fun h => evaluate (OriginalEncodedHeadConversion.convert n) (ofFn ![h])))
        (pairs c (pairs d (pairs e f))))).map (Nat.pair 5)) := by
  change evaluate OriginalNumberedEnumerationBranch.branch
    (ofFn ![numbersNumber a,evaluate (convertedHeads n) (ofFn ![numbersNumber b]),
      numbersNumber c,numbersNumber d,numbersNumber e,numbersNumber f]) = _
  rw [convertedValue]
  exact rawBranchValue _ _ _ _ _ _
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.NativeSupportProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEncodedNumberedEnumerationBranch.NativeSupportProof
