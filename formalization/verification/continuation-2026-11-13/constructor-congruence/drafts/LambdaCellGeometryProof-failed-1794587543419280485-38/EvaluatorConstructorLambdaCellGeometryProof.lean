module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaDeletedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorDeletionMetadataProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPositionStructuralKeyLambdaGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedApplicationErasureProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellGeometryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorErasureDefinitions EvaluatorConstructorInductionDefinitions
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atGeometry (R : Program 2) (H G : Program 1) (M W : Program 2)
 (count : OTerm alpha) (xs : Fin 11 → OTerm alpha)
 (cutoff d deleted newParameter erasedLeft erasedRight erasedChildLeft erasedChildRight
  childDeleted newChildParameter arrow a b : OTerm alpha)
 (hIH : Nonempty (Derivation body Delta (BelowLength R H G M W (suc count))))
 (hf : Nonempty (Derivation body Delta (lambdaFields R H G M W (suc count) xs)))
 (hb : Nonempty (Derivation body Delta (OriginalContextInsertion.Below cutoff (suc count))))
 (hk : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d cutoff (xs 9))))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted cutoff (xs 9))))
 (hn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newParameter (xs 8) deleted)))
 (heL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedLeft d cutoff (xs 0))))
 (heR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedRight d cutoff (xs 1))))
 (heCL : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedChildLeft d (suc cutoff) (xs 2))))
 (heCR : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedChildRight d (suc cutoff) (xs 3))))
 (hcons : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode childDeleted (xs 4) deleted)))
 (hcn : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing newChildParameter (xs 8) childDeleted)))
 (harr : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow arrow (xs 4) (xs 5))))
 (hclen : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (suc (suc count)) (xs 10))))
 (hccut : Nonempty (Derivation body Delta (OriginalContextInsertion.Below (suc cutoff) (suc (suc count)))))
 (hck : Nonempty (Derivation body Delta (graph2 InternalRawListRecursion.lookup d (suc cutoff) (xs 10))))
 (hcd : Nonempty (Derivation body Delta (graph2 OriginalClassContextAllPositionObserver.deleteAt childDeleted (suc cutoff) (xs 10))))
 (ha : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) a cutoff (xs 0) (xs 6))))
 (hbb : Nonempty (Derivation body Delta (graph3 (OriginalHereditaryDeletionRows.observation (OriginalHereditaryEvaluatorDefinitions.evaluator R)) b cutoff (xs 1) (xs 6))))
 : Nonempty (Derivation body Delta (InternalTagArithmeticSyntaxProof.eqn a b)) := by
 have h0 := andLeft hf
 have h1 := andLeft (andRight hf)
 have h2 := andLeft (andRight (andRight hf))
 have h3 := andLeft (andRight (andRight (andRight hf)))
 have h4 := andLeft (andRight (andRight (andRight (andRight hf))))
 have h5 := andLeft (andRight (andRight (andRight (andRight (andRight hf)))))
 have h6 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hf))))))
 have h7 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf)))))))
 have h8 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf))))))))
 have h9 := andLeft (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf)))))))))
 have h10 := (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight (andRight hf))))))))))
 have meta := EvaluatorConstructorDeletionMetadataProof.atSuccessor count (xs 9) cutoff deleted d h10 hb hd hk
 have fieldsL := OriginalLambdaConstructorGraphFieldsProof.constructorFields (xs 0) (xs 4) (xs 5) (xs 2) arrow h5 h7 harr
 have fieldsR := OriginalLambdaConstructorGraphFieldsProof.constructorFields (xs 1) (xs 4) (xs 5) (xs 3) arrow h6 h8 harr
 have conL := OriginalPositionStructuralKeyLambdaGeometryProof.erasedConstructor (xs 0) erasedLeft (xs 2) erasedChildLeft
   (xs 4) (xs 5) arrow d cutoff deleted (xs 9) fieldsL heL heCL meta.1
 have conR := OriginalPositionStructuralKeyLambdaGeometryProof.erasedConstructor (xs 1) erasedRight (xs 3) erasedChildRight
   (xs 4) (xs 5) arrow d cutoff deleted (xs 9) fieldsR heR heCR meta.1
 have typeL := OriginalPackedApplicationErasureProof.eraseTypeCopy (xs 2) erasedChildLeft (xs 5) d (suc cutoff) h7 heCL
 have typeR := OriginalPackedApplicationErasureProof.eraseTypeCopy (xs 3) erasedChildRight (xs 5) d (suc cutoff) h8 heCR
 let ys : Fin 11 → OTerm alpha := ![erasedLeft,erasedRight,erasedChildLeft,erasedChildRight,
   xs 4,xs 5,newParameter,newChildParameter,xs 8,deleted,childDeleted]
 have pair := EvaluatorConstructorLambdaDeletedProof.atCoordinates R H G M W
   (xs 0) (xs 1) (xs 2) (xs 3) (xs 6) (xs 7) (xs 8) (xs 9) deleted (xs 10) childDeleted
   cutoff d (suc count) count (suc (suc count)) ys
   hIH meta.2.2 h0 h1 h9 h2 hn meta.1 h4 hcn hclen hccut hck hcd
   heL heR heCL heCR hcons conL conR typeL typeR meta.2.1 rfl rfl rfl
 exact EvaluatorConstructorCellProof.atGeometry R (xs 0) (xs 1) erasedLeft erasedRight
   (xs 6) newParameter (xs 8) (xs 9) deleted cutoff d a b h2 hn hk hd heL heR
   (andRight (andRight pair)) ha hbb
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellGeometryProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellGeometryProof
