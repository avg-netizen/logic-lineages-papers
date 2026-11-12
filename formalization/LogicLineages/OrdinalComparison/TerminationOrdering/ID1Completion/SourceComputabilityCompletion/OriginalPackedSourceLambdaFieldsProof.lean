module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseLambdaCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open OriginalTypedDecoderTransportLogicalProof (iffForward)
open OriginalTypedDecoderInternalListProof (listTail)
open OriginalTransparentDecoderValidatorCollapseLambdaCoordinatesProof
open OriginalLambdaConstructorGraphSupportProof (bodyCodeValue)
open OriginalLambdaConstructorGraphSyntaxProof (oneRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem sourceFieldsCases (H G : Program 1) (M W : Program 2)
 (packed parameter : OTerm alpha) (psi : Formula alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) packed parameter)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalLambdaConstructor.tag (numeral 1) packed)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (d e child arrow : OTerm beta),
   (∀ p ∈ Delta, p.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (OriginalLambdaConstructor.Fields (packed.relabel j) d e child arrow)) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 apply OriginalTransparentDecoderValidatorCollapseLambdaCasesProof.lambdaCoordinatesCases packed parameter psi htag
 intro beta j Theta typ payload middle domain bodyPayload requestedDomain codomain c gamma extended child childParam hj hp ht hm hf hparam he hchild hcp
 have hs' := renameInto hs j Theta hj
 simp only [graph2Rename,oneRename] at hs'
 have factors := iffForward
   (OriginalTransparentDecoderValidatorCollapseSourceLambdaPackedProof.sourceLambdaCoordinatesIff H G M W
     (packed.relabel j) (parameter.relabel j) typ payload middle domain bodyPayload requestedDomain codomain
     child c gamma extended childParam hp ht hm hf hchild hparam he hcp) hs'
 have shape := lambdaShapeBackward (packed.relabel j) typ payload middle domain bodyPayload requestedDomain codomain
   hp ht hm hf (andRight (andRight (andLeft factors)))
 have hleft := InternalApplicationCertificateConstructorsSupportProof.pairLeft (packed.relabel j) typ payload hp
 have hdomain := rawDomainValue (packed.relabel j) typ payload middle domain bodyPayload hp ht hm
 have harrow := shapeArrowRecover (packed.relabel j) typ domain codomain hleft hdomain
   (listTail typ requestedDomain codomain hf) shape
 have hb := bodyCodeValue child codomain (packed.relabel j) bodyPayload hchild
   (rawBodyPayloadValue (packed.relabel j) typ payload middle domain bodyPayload hp ht hm)
 have fields : Nonempty (Derivation body Theta (OriginalLambdaConstructor.Fields (packed.relabel j) domain codomain child typ)) :=
   andIntro (rawTagValue (packed.relabel j) typ payload middle hp ht)
     (andIntro hleft (andIntro harrow (andIntro hdomain hb)))
 exact next beta j Theta domain codomain child typ hj fields

theorem actualFieldsCases : OriginalPackedSourceLambdaFieldsTargets.ActualFieldsCases := by
 intro body alpha Delta H G M W packed parameter psi hs ht next
 exact sourceFieldsCases H G M W packed parameter psi hs ht next
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalPackedSourceLambdaFieldsProof
