module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentObservationsInternalConsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListMapProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalUniformVertexPathSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalUnpairReverseProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendListProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecDecompositionSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderCoreProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionClosureLogicProof
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof (z eqn)
open InternalTagArithmeticSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalOriginalUniformVertexPathSupportProof (ternaryValue)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalTypedArgumentPrefixBuilder OriginalTypedArgumentPrefixBuilderRowDefinitions OriginalTypedArgumentPrefixBuilderBindingProof OriginalTypedArgumentObservations
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem stepValue (packed typ child tailBuilt suffix out : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (hc : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor out typ child tailBuilt))) :
 Nonempty (Derivation body Delta (graph3 OriginalTypedArgumentPrefixBuilder.step out packed tailBuilt suffix)) := by
 let xs : Fin 3 → OTerm alpha := Fin.cons packed (Fin.cons tailBuilt (Fin.cons suffix Fin.elim0))
 have hl := unaryValue InternalUnpair.left (.projection 0) typ packed xs (pairLeft _ _ _ hp) (projectionValue 0 xs)
 have hr := unaryValue InternalUnpair.right (.projection 0) child packed xs (pairRight _ _ _ hp) (projectionValue 0 xs)
 simpa only [OriginalTypedArgumentPrefixBuilder.step,leftOf,rightOf,graph3,xs] using ternaryValue OriginalRawSyntaxTransport.consConstructor
   (leftOf (.projection 0)) (rightOf (.projection 0)) (.projection 1) out typ child tailBuilt xs hc hl hr (projectionValue 1 xs)

theorem cellValue (R : Program 2) (packed typ child value typed parameter : OTerm alpha)
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ child)))
 (hv : Nonempty (Derivation body Delta (graph2 R value packed parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ value))) :
 Nonempty (Derivation body Delta (graph2 (cell R) typed packed parameter)) := by
 let xs : Fin 2 → OTerm alpha := Fin.cons packed (Fin.cons parameter Fin.elim0)
 have hl := unaryValue InternalUnpair.left (.projection 0) typ packed xs (pairLeft _ _ _ hp) (projectionValue 0 xs)
 have hr := binaryValue R (.projection 0) (.projection 1) value packed parameter xs hv (projectionValue 0 xs) (projectionValue 1 xs)
 simpa only [cell,pairOf,leftOf,graph2,xs] using binaryValue InternalPairing.pairing (leftOf (.projection 0))
   (.composition R ![.projection 0,.projection 1]) typed typ value xs ht hl hr

theorem atValues (R : Program 2)
 (raw head tail suffix built parameter mappedValue suffixValue total typ child value typed tailBuilt tailMapped tailTotal candidate : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (BelowRaw R raw)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode raw head tail)))
 (hf : Nonempty (Derivation body Delta (fields R raw suffix built parameter mappedValue suffixValue total)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing head typ child)))
 (hv : Nonempty (Derivation body Delta (graph2 R value head parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ value)))
 (hb : Nonempty (Derivation body Delta (graph2 build tailBuilt tail suffix)))
 (hm : Nonempty (Derivation body Delta (graph2 (mapped R) tailMapped tail parameter)))
 (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append tailTotal tailMapped suffixValue)))
 (hcan : Nonempty (Derivation body Delta (graph3 OriginalRawSyntaxTransport.consConstructor candidate typ child tailBuilt))) :
 Nonempty (Derivation body Delta (graph2 (argumentObservations R) total built parameter)) := by
 have hs := stepValue head typ child tailBuilt suffix candidate hp hcan
 have hbcan := InternalRawListRecursionProof.consValue (.projection (0 : Fin 1)) OriginalTypedArgumentPrefixBuilder.step
   raw head tail tailBuilt candidate (Fin.cons suffix Fin.elim0) hc hb hs
 have he := valueUnique build candidate built (Fin.cons raw (Fin.cons suffix Fin.elim0)) hbcan (andLeft hf)
 have htcell := cellValue R head typ child value typed parameter hp hv ht
 have hmap := InternalListMapProof.consForward (cell R) raw head tail typed tailMapped mappedValue
   (Fin.cons parameter Fin.elim0) hc htcell hm (andLeft (andRight hf))
 have happ := InternalApplicationValidityStackAppendListProof.consForward mappedValue typed tailMapped suffixValue tailTotal total
   hmap ha (andRight (andRight (andRight hf)))
 have hbound := InternalListCodecDecompositionSupportProof.consTailDescent raw head tail hc
 have hchild := belowRawApply R raw tail suffix tailBuilt parameter tailMapped suffixValue tailTotal hi hbound
   (andIntro hb (andIntro hm (andIntro (andLeft (andRight (andRight hf))) ha)))
 have hres := OriginalTypedArgumentObservationsInternalConsProof.backward R candidate typ child tailBuilt head value typed tailTotal parameter total
   hcan hp hv ht hchild happ
 exact headTransport (argumentObservations R) total candidate built (Fin.cons parameter Fin.elim0) he hres

theorem atZero (R : Program 2) (raw suffix built parameter mappedValue suffixValue total : OTerm alpha)
 (hz : Nonempty (Derivation body Delta (eqn raw z)))
 (hf : Nonempty (Derivation body Delta (fields R raw suffix built parameter mappedValue suffixValue total))) :
 Nonempty (Derivation body Delta (graph2 (argumentObservations R) total built parameter)) := by
 have hb := headTransport build built raw z (Fin.cons suffix Fin.elim0) hz (andLeft hf)
 have hm := headTransport (mapped R) mappedValue raw z (Fin.cons parameter Fin.elim0) hz (andLeft (andRight hf))
 have hb0 := InternalRawListRecursionProof.nilValue (body := body) (Gamma := Delta) (.projection (0 : Fin 1)) OriginalTypedArgumentPrefixBuilder.step suffix
   (Fin.cons suffix Fin.elim0) (projectionValue 0 (Fin.cons suffix Fin.elim0))
 have heB := valueUnique build built suffix (Fin.cons z (Fin.cons suffix Fin.elim0)) hb hb0
 have hm0 := InternalRawListRecursionProof.nilValue (body := body) (Gamma := Delta) InternalRawListRecursion.zero (InternalListMap.mapStep (cell R)) z
   (Fin.cons parameter Fin.elim0) (InternalAcceptanceConjunctionProof.constantZeroValue (Fin.cons parameter Fin.elim0))
 have heM := valueUnique (mapped R) mappedValue z (Fin.cons z (Fin.cons parameter Fin.elim0)) hm hm0
 have ha := headTransport InternalApplicationValidityStackAppend.append total mappedValue z (Fin.cons suffixValue Fin.elim0)
   heM (andRight (andRight (andRight hf)))
 obtain ⟨heT⟩ := InternalApplicationValidityStackAppendListProof.appendZeroRecover total suffixValue ha
 obtain ⟨heB⟩ := heB
 have h := headTransport (argumentObservations R) suffixValue suffix built (Fin.cons parameter Fin.elim0)
   ⟨symm heB⟩ (andLeft (andRight (andRight hf)))
 exact outputTransport (argumentObservations R) suffixValue total (Fin.cons built (Fin.cons parameter Fin.elim0)) ⟨symm heT⟩ h
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderCoreProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedArgumentPrefixBuilderCoreProof
