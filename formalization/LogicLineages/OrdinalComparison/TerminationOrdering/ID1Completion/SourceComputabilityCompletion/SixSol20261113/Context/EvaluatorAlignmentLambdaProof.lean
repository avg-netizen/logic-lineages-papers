module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSharedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSharedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentAssemblyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentParameterProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentLambdaProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof InternalControlGraphSupportProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open EvaluatorChildrenSharedProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open SixSol20261113.Erasure.EvaluatorErasureDefinitions
open SixSol20261113.Erasure.EvaluatorErasureSyntax

theorem actualLambda : EvaluatorAlignmentTargets.ActualLambda := by
 intro R H G M W body alpha Delta left right parameter ld lc child lp rd rc otherChild rp had hl hr
 have htl := EvaluatorChildrenSelectorWiring.tag body alpha Delta (numeral 1) left parameter (andLeft hl)
 have htr := EvaluatorChildrenSelectorWiring.tag body alpha Delta (numeral 1) right parameter (andLeft hr)
 have hdl := EvaluatorChildrenSelectorWiring.domain body alpha Delta ld left parameter (andLeft (andRight hl))
 have hdr := EvaluatorChildrenSelectorWiring.domain body alpha Delta rd right parameter (andLeft (andRight hr))
 have hcl := EvaluatorChildrenSelectorWiring.codomain body alpha Delta lc left parameter (andLeft (andRight (andRight hl)))
 have hcr := EvaluatorChildrenSelectorWiring.codomain body alpha Delta rc right parameter (andLeft (andRight (andRight hr)))
 have he := EvaluatorAlignmentAssemblyProof.lambda R H G M W left right parameter ld lc rd rc had htl hdl hcl htr hdr hcr
 have hed := andLeft he
 rw [equalEqn] at hed
 have hdrSame := outputTransport OriginalRootObservation.domain rd ld (![right,parameter])
   (by obtain ⟨hed⟩ := hed; exact ⟨InternalTagArithmeticSupportProof.symm hed⟩) hdr
 have hpl := EvaluatorChildrenSelectorLambdaProof.parameterAt left parameter ld lp
   (andLeft (andRight hl)) (andRight (andRight (andRight (andRight hl))))
 have hpr := EvaluatorChildrenSelectorLambdaProof.parameterAt right parameter rd rp
   (andLeft (andRight hr)) (andRight (andRight (andRight (andRight hr))))
 have hp := EvaluatorAlignmentParameterProof.commonDomain left right parameter ld lp rp hdl hdrSame hpl hpr
 exact andIntro (andLeft he) (andIntro (andRight he) hp)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentLambdaProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentLambdaProof
