module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleShapeProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentTermTagsProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapsePackedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRootObservationDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSourceTagsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalApplicationValidityStackAppendInductionCoreProof (formulaCases withHyp)
open InternalQuotientComparisonProof (orLeft orRight)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalUniverseDecoderInternalAcceptance OriginalTypedDecoderStepSpecification
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open OriginalTransparentDecoderValidatorCollapsePackedProof
attribute [local irreducible] programGraph
theorem sourceTags (H G : Program 1) (M W : Program 2)
 (input parameter tag : OTerm alpha)
 (hs : Nonempty (Derivation body Delta (graph2 (OriginalUniverseDecoder.source H G M W) (numeral 1) input parameter)))
 (ht : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag tag input parameter))) :
 Nonempty (Derivation body Delta (equal tag (numeral 0) ⊔ (equal tag (numeral 1) ⊔ (equal tag (numeral 2) ⊔ (equal tag (numeral 3) ⊔ (equal tag (numeral 4) ⊔ equal tag (numeral 5))))))) := by
 apply packedCases input parameter
 intro beta j Theta typ raw c gamma hj hp hparam
 have hs' := renameInto hs j Theta hj
 have ht' := renameInto ht j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hs' ht'
 have ha := andRight (sourceFieldsElim H G M W (input.relabel j) (parameter.relabel j) typ raw c gamma hp hparam hs')
 let xs : Fin 2 → OTerm beta := ![input.relabel j,parameter.relabel j]
 have hraw := pairRightValue (.projection 0) (input.relabel j) typ raw xs (projectionValue 0 xs) hp
 have htag := unaryRecover InternalUnpair.left OriginalRootObservation.raw (tag.relabel j) raw xs ht' hraw
 apply programCases InternalUnpair.right (Fin.cons raw Fin.elim0) _
 intro beta' k Xi payload hk hpay
 have ha' := renameInto ha k Xi hk
 rw [OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] at ha'
 have htag' := renameInto htag k Xi hk
 rw [graph1Rename] at htag'
 simp only [consTermRename,emptyRename] at hpay
 have hpair := InternalApplicationCertificateConstructorsSupportProof.reconstructPair
   (raw.relabel k) ((tag.relabel j).relabel k) payload htag' hpay
 have htags := EvaluatorAlignmentTermTagsProof.termTags H M W (raw.relabel k)
   ((tag.relabel j).relabel k) payload (typ.relabel k) (gamma.relabel k) (c.relabel k) hpair ha'
 simpa only [OriginalUniverseDecoderInternalBooleanProof.orRename,
   OriginalTypedDecoderInternalLogicSyntaxProof.equalRename,GuardedSourceSyntaxProof.numeralRename] using htags
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSourceTagsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSourceTagsProof
