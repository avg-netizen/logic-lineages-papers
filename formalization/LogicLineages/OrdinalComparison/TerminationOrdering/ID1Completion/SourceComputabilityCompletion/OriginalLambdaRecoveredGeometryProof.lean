module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphReconstructionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNonApplicationSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalGraphComposition InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalApplicationStepPeelSupportProof InternalStructuralEndpointGuardSupportProof
open InternalTagArithmeticSyntaxProof (z suc)
open OriginalLambdaGuardLeaf
open OriginalLambdaConstructorGraphSyntaxProof (queryCases fieldsRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Accepted matching fields recover the actual target lambda geometry;
no target constructor is a premise. -/
theorem targetFields (s t cert parameter oldChild childT d e arrow : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e oldChild arrow)))
 (hm : Nonempty (Derivation body Delta (graph4 matchingTarget (suc z) s t cert parameter)))
 (hb : Nonempty (Derivation body Delta (graph4 targetBody childT s t cert parameter))) :
 Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields t d e childT arrow)) := by
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 have hm0 := conjunctionRecover targetLambda _ xs hm
 have hm1 := conjunctionRecover _ _ xs (andRight hm0)
 have htype := unaryValue InternalUnpair.left (.projection 0) arrow s xs
   (andLeft (andRight hs)) (projectionValue 0 xs)
 have hd := unaryValue OriginalLambdaConstructor.domain (.projection 0) d s xs
   (andLeft (andRight (andRight (andRight hs)))) (projectionValue 0 xs)
 have htType := sameRightRecover (leftOf (.projection 1)) (leftOf (.projection 0)) arrow xs
   (andLeft hm1) htype
 have htDom := sameRightRecover (.composition OriginalLambdaConstructor.domain (fun _ : Fin 1 => .projection 1))
   sourceDomain d xs (andRight hm1) hd
 have htTest := unaryRecover lambdaTest (.projection 1) (suc z) t xs
   (andLeft hm0) (projectionValue 1 xs)
 have htTag := sameRightRecover OriginalLambdaConstructor.tag (InternalLessThan.constantOne 1)
   (suc z) (Fin.cons t Fin.elim0) htTest (InternalLessThanSupportProof.oneConstantValue _)
 have ha := andLeft (andRight (andRight hs))
 have htail := andLeft (andRight (InternalListCodecSupportProof.consDestruction arrow d e ha))
 have hcod := unaryValue InternalListCodec.tailCode (leftOf (.projection 0)) e arrow xs htail htype
 have htBody := binaryRecover OriginalLambdaConstructor.bodyCode sourceCodomain (.projection 1)
   childT e t xs hb hcod (projectionValue 1 xs)
 exact andIntro htTag (andIntro
   (unaryRecover InternalUnpair.left (.projection 1) arrow t xs htType (projectionValue 1 xs))
   (andIntro ha (andIntro
    (unaryRecover OriginalLambdaConstructor.domain (.projection 1) d t xs htDom (projectionValue 1 xs)) htBody)))

theorem sourceChildEquality (s t cert parameter oldChild childS d e arrow : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e oldChild arrow)))
 (hc : Nonempty (Derivation body Delta (graph4 sourceBody childS s t cert parameter))) :
 Nonempty (Derivation body Delta (equal childS oldChild)) := by
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 have htype := unaryValue InternalUnpair.left (.projection 0) arrow s xs
   (andLeft (andRight hs)) (projectionValue 0 xs)
 have htail := andLeft (andRight (InternalListCodecSupportProof.consDestruction arrow d e
   (andLeft (andRight (andRight hs)))))
 have hcod := unaryValue InternalListCodec.tailCode (leftOf (.projection 0)) e arrow xs htail htype
 have hv := binaryValue OriginalLambdaConstructor.bodyCode sourceCodomain (.projection 0)
   oldChild e s xs (andRight (andRight (andRight (andRight hs)))) hcod (projectionValue 0 xs)
 obtain ⟨h⟩ := valueUnique sourceBody childS oldChild xs hc hv
 exact ⟨by simpa only [equalEqn] using h⟩

theorem parameterAtExtension (s t cert parameter oldChild childParam d e arrow context gamma extended : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e oldChild arrow)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter context gamma)))
 (he : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode extended d gamma)))
 (hc : Nonempty (Derivation body Delta (graph4 childParameter childParam s t cert parameter))) :
 Nonempty (Derivation body Delta (graph2 InternalPairing.pairing childParam context extended)) := by
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 have hcontext := unaryValue InternalUnpair.left (.projection 3) context parameter xs
   (pairLeft parameter context gamma hp) (projectionValue 3 xs)
 have hgamma := unaryValue InternalUnpair.right (.projection 3) gamma parameter xs
   (pairRight parameter context gamma hp) (projectionValue 3 xs)
 have hdomain := unaryValue OriginalLambdaConstructor.domain (.projection 0) d s xs
   (andLeft (andRight (andRight (andRight hs)))) (projectionValue 0 xs)
 have hextended := binaryValue InternalListCodec.consCode sourceDomain (rightOf (.projection 3))
   extended d gamma xs he hdomain hgamma
 exact binaryRecover InternalPairing.pairing (leftOf (.projection 3))
   (consOf sourceDomain (rightOf (.projection 3))) childParam context extended xs hc hcontext hextended

theorem actualOriginalLambdaRecoveredGeometry :
 OriginalLambdaRecoveredGeometryTargets.ActualOriginalLambdaRecoveredGeometry := by
 intro body alpha Delta leaf s t cert parameter oldChild childS childT childCert childParam d e arrow context gamma psi hs hp hr continuation
 have hsource := andLeft (andRight (andRight (andRight hr)))
 have htarget := andLeft (andRight (andRight (andRight (andRight hr))))
 have hparameter := andLeft (andRight (andRight (andRight (andRight (andRight (andRight hr))))))
 have hleaf := andRight (andRight (andRight (andRight (andRight (andRight (andRight hr))))))
 have heq := sourceChildEquality s t cert parameter oldChild childS d e arrow hs hsource
 have ht := targetFields s t cert parameter oldChild childT d e arrow hs (andLeft hr) htarget
 have hctor := OriginalLambdaConstructorGraphReconstructionProof.constructorReconstruction t d e childT arrow ht
 let qs : Fin 1 → Program 2 := fun _ => InternalListCodec.consCode
 let xs : Fin 2 → OTerm alpha := Fin.cons d (Fin.cons gamma Fin.elim0)
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
 intro beta j ys Theta hj hq
 apply continuation beta j Theta (ys 0) hj
 have hs' := renameInto hs j Theta hj
 rw [fieldsRename] at hs'
 have hp' := renameInto hp j Theta hj
 rw [graph2Rename] at hp'
 have hc' := renameInto hparameter j Theta hj
 rw [graph4Rename] at hc'
 have he : Nonempty (Derivation body Theta
   (graph2 InternalListCodec.consCode (ys 0) (d.relabel j) (gamma.relabel j))) := by
   simpa only [qs, xs, InternalRecursionGraphStepSyntaxProof.consTermRename, emptyRename] using hq 0
 have hcp := parameterAtExtension (s.relabel j) (t.relabel j) (cert.relabel j)
   (parameter.relabel j) (oldChild.relabel j) (childParam.relabel j)
   (d.relabel j) (e.relabel j) (arrow.relabel j) (context.relabel j) (gamma.relabel j) (ys 0)
   hs' hp' he hc'
 have heq' := renameInto heq j Theta hj
 have ht' := renameInto ht j Theta hj
 rw [fieldsRename] at ht'
 have hctor' := renameInto hctor j Theta hj
 rw [graph3Rename] at hctor'
 have hleaf' := renameInto hleaf j Theta hj
 simp only [graph4Rename, InternalOriginalStepGuard.one, InternalTagArithmeticSyntaxProof.sucRelabel, InternalTagArithmeticSyntaxProof.zRelabel] at hleaf'
 exact andIntro (by simpa only [OriginalTypedDecoderInternalLogicSyntaxProof.equalRename] using heq')
   (andIntro ht' (andIntro hctor' (andIntro he (andIntro hcp hleaf'))))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryProof

#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryProof
