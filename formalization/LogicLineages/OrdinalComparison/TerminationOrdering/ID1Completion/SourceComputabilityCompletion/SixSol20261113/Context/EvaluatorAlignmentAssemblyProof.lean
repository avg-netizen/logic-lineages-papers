module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSharedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentSharedProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorChildrenSelectorProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentAssemblyProof
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

theorem application (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter ld lc rd rc : OTerm alpha)
 (had : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) left parameter)))
 (hdl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain ld left parameter)))
 (hcl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType lc left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 2) right parameter)))
 (hdr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain rd right parameter)))
 (hcr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.resultType rc right parameter))) :
 Nonempty (Derivation body Delta (equal ld rd ⊓ equal lc rc)) := by
 apply sameCases R left right parameter _ (andRight (andRight had))
 intro beta j Theta out hj hv
 have hsl' := renameInto (andLeft had) j Theta hj
 have hsr' := renameInto (andLeft (andRight had)) j Theta hj
 have htl' := renameInto htl j Theta hj
 have hdl' := renameInto hdl j Theta hj
 have hcl' := renameInto hcl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hdr' := renameInto hdr j Theta hj
 have hcr' := renameInto hcr j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' htl' hdl' hcl' htr' hdr' hcr'
 have he := EvaluatorAlignmentSharedProof.application R H G M W (left.relabel j) (right.relabel j)
   (parameter.relabel j) out (ld.relabel j) (lc.relabel j) (rd.relabel j) (rc.relabel j)
   hsl' (andLeft hv) htl' hdl' hcl' hsr' (andRight hv) htr' hdr' hcr'
 simpa only [conjunctionRename,equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel] using he

theorem lambda (R : Program 2) (H G : Program 1) (M W : Program 2)
 (left right parameter ld lc rd rc : OTerm alpha)
 (had : Nonempty (Derivation body Delta (AdmittedPair R H G M W left right parameter)))
 (htl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) left parameter)))
 (hdl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain ld left parameter)))
 (hcl : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.codomain lc left parameter)))
 (htr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.tag (numeral 1) right parameter)))
 (hdr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.domain rd right parameter)))
 (hcr : Nonempty (Derivation body Delta (graph2 OriginalRootObservation.codomain rc right parameter))) :
 Nonempty (Derivation body Delta (equal ld rd ⊓ equal lc rc)) := by
 apply sameCases R left right parameter _ (andRight (andRight had))
 intro beta j Theta out hj hv
 have hsl' := renameInto (andLeft had) j Theta hj
 have hsr' := renameInto (andLeft (andRight had)) j Theta hj
 have htl' := renameInto htl j Theta hj
 have hdl' := renameInto hdl j Theta hj
 have hcl' := renameInto hcl j Theta hj
 have htr' := renameInto htr j Theta hj
 have hdr' := renameInto hdr j Theta hj
 have hcr' := renameInto hcr j Theta hj
 simp only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] at hsl' hsr' htl' hdl' hcl' htr' hdr' hcr'
 have he := EvaluatorAlignmentSharedProof.lambda R H G M W (left.relabel j) (right.relabel j)
   (parameter.relabel j) out (ld.relabel j) (lc.relabel j) (rd.relabel j) (rc.relabel j)
   hsl' (andLeft hv) htl' hdl' hcl' hsr' (andRight hv) htr' hdr' hcr'
 simpa only [conjunctionRename,equalEqn,InternalTagArithmeticSyntaxProof.eqnRelabel] using he

theorem actualApplication : EvaluatorAlignmentTargets.ActualApplication := by
 intro R H G M W body alpha Delta left right parameter ld lc lf la rd rc rf ra had hl hr
 exact application R H G M W left right parameter ld lc rd rc had
   (EvaluatorChildrenSelectorWiring.tag body alpha Delta (numeral 2) left parameter (andLeft hl))
   (EvaluatorChildrenSelectorWiring.domain body alpha Delta ld left parameter (andLeft (andRight hl)))
   (EvaluatorChildrenSelectorWiring.resultType body alpha Delta lc left parameter (andLeft (andRight (andRight hl))))
   (EvaluatorChildrenSelectorWiring.tag body alpha Delta (numeral 2) right parameter (andLeft hr))
   (EvaluatorChildrenSelectorWiring.domain body alpha Delta rd right parameter (andLeft (andRight hr)))
   (EvaluatorChildrenSelectorWiring.resultType body alpha Delta rc right parameter (andLeft (andRight (andRight hr))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentAssemblyProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.EvaluatorAlignmentAssemblyProof
