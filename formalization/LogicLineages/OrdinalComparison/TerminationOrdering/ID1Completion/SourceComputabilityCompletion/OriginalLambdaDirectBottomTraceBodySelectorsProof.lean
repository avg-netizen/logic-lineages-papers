module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaRecoveredGeometryTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentLambdaStepFieldsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphReconstructionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDirectBottomNonApplicationSpineProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalLogicSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBodySelectorsProof
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

/-- The body-specific scoped IH uses the same actual codomain selector as
both original leaf body programs. No target typing or context oracle. -/
theorem bodySelectors (s t cert parameter oldChild childS childT d e arrow : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (OriginalLambdaConstructor.Fields s d e oldChild arrow)))
 (hbs : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.bodyCode childS e s)))
 (hbt : Nonempty (Derivation body Delta (graph2 OriginalLambdaConstructor.bodyCode childT e t))) :
 Nonempty (Derivation body Delta
  (graph4 sourceBody childS s t cert parameter ⊓ graph4 targetBody childT s t cert parameter)) := by
 let xs : Fin 4 → OTerm alpha := Fin.cons s (Fin.cons t (Fin.cons cert (Fin.cons parameter Fin.elim0)))
 have htype := unaryValue InternalUnpair.left (.projection 0) arrow s xs
   (andLeft (andRight hs)) (projectionValue 0 xs)
 have htail := andLeft (andRight (InternalListCodecSupportProof.consDestruction arrow d e
   (andLeft (andRight (andRight hs)))))
 have hcod := unaryValue InternalListCodec.tailCode (leftOf (.projection 0)) e arrow xs htail htype
 have hsrc := binaryValue OriginalLambdaConstructor.bodyCode sourceCodomain (.projection 0)
   childS e s xs hbs hcod (projectionValue 0 xs)
 have htgt := binaryValue OriginalLambdaConstructor.bodyCode sourceCodomain (.projection 1)
   childT e t xs hbt hcod (projectionValue 1 xs)
 exact andIntro hsrc htgt
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBodySelectorsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaDirectBottomTraceBodySelectorsProof
