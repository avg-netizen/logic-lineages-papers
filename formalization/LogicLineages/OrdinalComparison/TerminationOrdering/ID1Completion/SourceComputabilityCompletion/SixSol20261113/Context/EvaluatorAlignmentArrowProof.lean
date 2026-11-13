module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalApplicationFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorWiring
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameIdentityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentArrowProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight queryCases)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalTagArithmeticSyntaxProof (suc z sucRelabel zRelabel)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
theorem liftedRecover (q : Program 1) (r : Program 2) (lifted : EvaluatorChildrenSelectorWiring.Lifted q r)
 (out parent parameter : OTerm alpha)
 (h : Nonempty (Derivation body Delta (graph2 r out parent parameter))) :
 Nonempty (Derivation body Delta (graph1 q out parent)) := by
 apply programCases q (Fin.cons parent Fin.elim0) _
 intro beta j Theta value hj hv
 rw [graph1Rename]
 have h' := renameInto h j Theta hj
 rw [graph2Rename] at h'
 simp only [consTermRename,emptyRename] at hv
 have hr := lifted body beta Theta value (parent.relabel j) (parameter.relabel j) hv
 have he := valueUnique r value (out.relabel j) (![parent.relabel j,parameter.relabel j]) hr h'
 exact outputTransport q value (out.relabel j) (Fin.cons (parent.relabel j) Fin.elim0) he hv

/-- Genuine source lambda typing reconstructs the packed arrow type from
actual original domain/codomain selector values. No typedness shortcut. -/
theorem sourceArrow (H G : Program 1) (M W : Program 2)
 (input parameter typ domain codomain : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) input parameter)))
 (htyp : Nonempty (Derivation body Delta (graph1 InternalUnpair.left typ input)))
 (hd : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain domain input parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.codomain codomain input parameter))) :
 Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.arrow typ domain codomain)) := by
 have htag := liftedRecover _ _ EvaluatorChildrenSelectorWiring.tag (numeral 1) input parameter ht
 apply OriginalPackedSourceLambdaFieldsProof.actualFieldsCases body alpha Delta H G M W input parameter _ hs htag
 intro beta j Theta d e child arrow hj hf
 rw [graph2Rename]
 have ht' := renameInto htyp j Theta hj
 have hd' := renameInto hd j Theta hj
 have hc' := renameInto hc j Theta hj
 rw [graph1Rename] at ht'
 rw [graph2Rename] at hd' hc'
 have ha := andLeft (andRight (andRight hf))
 have hactualType := andLeft (andRight hf)
 have hactualDomain := EvaluatorChildrenSelectorWiring.domain body beta Theta d (input.relabel j) (parameter.relabel j)
   (andLeft (andRight (andRight (andRight hf))))
 have htail := InternalRawListRecursionSupportProof.consTail arrow d e ha
 have hactualCodomain := unaryValue InternalListCodec.tailCode OriginalRootObservation.resultType e arrow
   (![input.relabel j,parameter.relabel j]) htail
   (EvaluatorChildrenSelectorWiring.resultType body beta Theta arrow (input.relabel j) (parameter.relabel j) hactualType)
 have et := valueUnique InternalUnpair.left arrow (typ.relabel j) (Fin.cons (input.relabel j) Fin.elim0) hactualType ht'
 have ed := valueUnique OriginalRootObservation.domain d (domain.relabel j) (![input.relabel j,parameter.relabel j]) hactualDomain hd'
 have ec := valueUnique OriginalRootObservation.codomain e (codomain.relabel j) (![input.relabel j,parameter.relabel j]) hactualCodomain hc'
 have hout := outputTransport OriginalLambdaConstructor.arrow arrow (typ.relabel j) (![d,e]) et ha
 exact SixSol20261113.Runtime.PrefixFrameIdentityProof.binaryInputs OriginalLambdaConstructor.arrow
   (typ.relabel j) d e (domain.relabel j) (codomain.relabel j) ed ec hout
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentArrowProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentArrowProof
