module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHeadClassNumberNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalNumericListSortNativeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderEvaluationSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalRootObservation InternalApplicationCertificateConstructors
open InternalApplicationCertificateConstructorsEvaluationProof InternalListCodecEvaluationProof
open OriginalTypedDecoderEvaluationSupportProof OriginalRawSyntaxTransportEvaluationSupportProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo)
attribute [local irreducible] InternalPairing.pairing InternalUnpair.left InternalUnpair.right InternalListCodec.consCode

theorem firstProjection (x y : Nat) : evaluate (.projection (0 : Fin 2)) (x ::ᵥ y ::ᵥ nil) = x := rfl
theorem secondProjection (x y : Nat) : evaluate (.projection (1 : Fin 2)) (x ::ᵥ y ::ᵥ nil) = y := rfl

theorem typedEvaluation (R : Program 2) (typ child param : Program 2) (v : List.Vector Nat 2) :
 evaluate (typed R typ child param) v = Nat.pair (evaluate typ v)
   (evaluate R (evaluate child v ::ᵥ evaluate param v ::ᵥ nil)) := by
 rw [typed,pairOfEvaluation,binaryCompositionEvaluation,vectorTwo]
 rfl

theorem argumentsEvaluation (R : Program 2) {n : Nat} {arity : Fin n → Nat} {Gamma types : List Ty}
 (c : Nat) (args : AuxArguments (Fin n) arity Gamma types) :
 evaluate (OriginalTypedArgumentObservations.argumentObservations R)
   (codeNumber (argumentsCode args) ::ᵥ Nat.pair c (typesNumber Gamma) ::ᵥ nil) =
 numbersNumber (argumentValues R c args) := by
 change evaluate (OriginalTypedArgumentObservations.argumentObservations R)
   (codeNumber (argumentsCode args) ::ᵥ Nat.pair c (typesNumber Gamma) ::ᵥ nil) =
   numbersNumber ((argumentList args).map (fun q => Nat.pair (typeNumber q.1)
     (evaluate R (ofFn ![packedNumber q,Nat.pair c (typesNumber Gamma)]))))
 simpa [vectorTwo] using
   OriginalTypedArgumentObservationsNativeProof.nativeCalibration R n arity Gamma types args (Nat.pair c (typesNumber Gamma))

theorem headEvaluation {n : Nat} (h : Head (Fin n)) :
 evaluate OriginalHeadClassNumber.classNumber (headNumber (headCode h) ::ᵥ nil) =
 classNumber (RecursiveComparison.headClass h) := by
 rw [OriginalHeadClassNumberNativeProof.nativeCalibration]
 cases h <;> rfl

/-- Literal constructor calibration, retaining actual child parameters and
sorting only BASE observations. No correctness hypothesis on R is used. -/
theorem nativeCalibration : OriginalRootObservationTargets.NativeCalibration := by
 intro R n arity Gamma c q
 obtain ⟨tau,q⟩ := q
 cases q <;>
   simp only [rootObservation,ifSameEvaluation,tag,raw,packed,payload,resultType,
     parameter,domain,codomain,bodyPacked,childParameter,functionPacked,argumentPacked,
     variableCase,bottom,lambda,OriginalRootObservation.application,ordinary,numbered,numberedTail,
     tagged,headClass,sortedArguments,arguments,
     typedEvaluation,unaryCompositionEvaluation,binaryCompositionEvaluation,
     vectorOne,vectorTwo,pairOfEvaluation,leftOfEvaluation,rightOfEvaluation,consOfEvaluation,
     firstProjection,secondProjection,constantEvaluation,
     packedNumber,termCode,codeNumber,typeNumber,typesNumber,
     Nat.unpair_pair,Nat.add_sub_cancel_left,
     tailEvaluation,argumentsEvaluation,headEvaluation,
     OriginalNumericListSortNativeProof.nativeCalibration,
     nativeValue,typedValue,argumentValues]
 all_goals try simp only [Fin.cons_zero,Fin.cons_succ] at *
 all_goals simp [Nat.add_sub_cancel_left,Nat.unpair_pair,headEvaluation,argumentsEvaluation,
   OriginalNumericListSortNativeProof.nativeCalibration,argumentValues]
 all_goals exact OriginalNumericListSortNativeProof.nativeCalibration _
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationNativeProof
