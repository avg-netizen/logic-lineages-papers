module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationNativeProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnNativeProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open Source Source.SourceMarkedSyntax NumberedRewriteSyntax NumberedRewriteReduction
open NumberedLeastCodeRepresentative NumberedAuxiliaryCoding NumberedMultisetNumeric
open OriginalHereditaryReturn
open InternalApplicationCertificateConstructorsEvaluationProof InternalListCodecEvaluationProof
open OriginalTypedDecoderEvaluationSupportProof OriginalRawSyntaxTransportEvaluationSupportProof
open InternalEqualityTestEvaluationProof (vectorOne vectorTwo vectorThree)
attribute [local irreducible] InternalPairing.pairing InternalUnpair.left InternalUnpair.right InternalListCodec.consCode

theorem firstProjection (x y z : Nat) :
  evaluate (.projection (0 : Fin 3)) (x ::ᵥ y ::ᵥ z ::ᵥ nil) = x := rfl
theorem secondProjection (x y z : Nat) :
  evaluate (.projection (1 : Fin 3)) (x ::ᵥ y ::ᵥ z ::ᵥ nil) = y := rfl
theorem thirdProjection (x y z : Nat) :
  evaluate (.projection (2 : Fin 3)) (x ::ᵥ y ::ᵥ z ::ᵥ nil) = z := rfl

/-- A finite return algebra with genuine already-evaluated child slots. -/
theorem rootSubstitution : OriginalHereditaryReturnTargets.RootSubstitution := by
  intro Q n arity Gamma c q
  rw [OriginalRootObservationNativeProof.nativeCalibration]
  obtain ⟨tau,q⟩ := q
  cases q <;>
    simp only [returnRoot,ifSameEvaluation,typ,payload,tag,domain,codomain,
      tagged,typed,sorted,headClass,numberedTail,slots,scalar,
      unaryCompositionEvaluation,binaryCompositionEvaluation,
      vectorOne,vectorTwo,vectorThree,pairOfEvaluation,leftOfEvaluation,rightOfEvaluation,
      consOfEvaluation,firstProjection,secondProjection,thirdProjection,constantEvaluation,
      packedNumber,termCode,codeNumber,typeNumber,typesNumber,
      Nat.unpair_pair,Nat.add_sub_cancel_left,tailEvaluation,
      OriginalRootObservationNativeProof.headEvaluation,
      OriginalNumericListSortNativeProof.nativeCalibration,
      OriginalRootObservation.nativeValue,OriginalRootObservation.typedValue]
  all_goals try simp only [Fin.cons_zero,Fin.cons_succ] at *
  all_goals simp [Nat.add_sub_cancel_left,Nat.unpair_pair,
    OriginalRootObservationNativeProof.headEvaluation,
    OriginalNumericListSortNativeProof.nativeCalibration,
    OriginalRootObservation.argumentValues]
  all_goals exact OriginalNumericListSortNativeProof.nativeCalibration _

/-- List assembly preserves order. BASE sorting happens in returnRoot only. -/
theorem argumentsConsSubstitution : OriginalHereditaryReturnTargets.ArgumentsConsSubstitution := by
  intro Q n arity Gamma c tau types q args
  simp only [returnArgumentsCons,consOfEvaluation,pairOfEvaluation,leftOfEvaluation,
    rightOfEvaluation,vectorThree,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail,Function.comp_apply,Fin.cons_zero,Fin.cons_succ,
    firstProjection,secondProjection,thirdProjection,
    argumentsCode,codeNumber,Nat.unpair_pair,OriginalRootObservation.argumentValues,
    argumentList,List.map_cons,numbersNumber,OriginalRootObservation.typedValue,scalar]
  rfl


end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnNativeProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryReturnNativeProof
