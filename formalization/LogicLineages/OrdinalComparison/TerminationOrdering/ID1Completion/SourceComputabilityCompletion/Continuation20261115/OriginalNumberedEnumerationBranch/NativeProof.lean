module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.Targets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportConstructorEvaluationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsEnumeration.CodecProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.NativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open NumberedMultisetNumeric NumberedMultisetNumericSupportProof
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding
open InternalApplicationCertificateConstructorsEvaluationProof
open OriginalRawSyntaxTransportEvaluationSupportProof
open InternalApplicationStepPeelEvaluationSupportProof (projectionEvaluation)
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

theorem branchValue (a b c d e f : List Nat) :
    evaluate branch (inputs a b c d e f) =
      numbersNumber ((pairs a (pairs b (pairs c (pairs d (pairs e f))))).map (Nat.pair 5)) := by
  change evaluate (InternalListMap.map tagPayload) (ofFn ![evaluate product123456 (inputs a b c d e f)]) = _
  rw [productValue,mapValue]

theorem typesEncoding (ts : List Source.Ty) : Encodable.encode ts = typesNumber ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [Encodable.encode_list_cons,ih]
    change 1 + Nat.pair (typeNumber t) (typesNumber ts) = typesNumber (t :: ts)
    rfl

theorem numberedEncoding (n : Nat) (k : Nat) (h : HeadCode (Fin n)) (t : Source.Ty)
    (b : Code (Fin n)) (ts : List Source.Ty) (e : Code (Fin n)) :
    Encodable.encode (Code.numbered k h t b ts e) =
      Nat.pair 5 (Nat.pair (Encodable.encode k) (Nat.pair (Encodable.encode h)
        (Nat.pair (Encodable.encode t) (Nat.pair (Encodable.encode b)
          (Nat.pair (Encodable.encode ts) (Encodable.encode e)))))) := by
  rw [typesEncoding]
  rfl

theorem nativeBranch : Targets.NativeBranch := by
  intro n labels heads types bases tuples extras
  simp only [OriginalTypeListsEnumeration.CodecProof.listEncoding]
  change evaluate branch (inputs (labels.map Encodable.encode) (heads.map Encodable.encode)
    (types.map Encodable.encode) (bases.map Encodable.encode) (tuples.map Encodable.encode)
    (extras.map Encodable.encode)) = _
  rw [branchValue]
  simp only [pairs,List.map_flatMap,List.flatMap_map,List.map_map]
  simp only [Function.comp_def,numberedEncoding]
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.NativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalNumberedEnumerationBranch.NativeProof
