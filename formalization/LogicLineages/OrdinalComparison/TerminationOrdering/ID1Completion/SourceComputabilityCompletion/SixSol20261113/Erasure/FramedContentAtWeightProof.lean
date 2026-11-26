module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentDependencyProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentBindingProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentLocalProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentAtWeightProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalAcceptanceSupportProof (programCases)
open InternalControlGraphSupportProof (emptyRename)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open OriginalHereditaryInternalAgendaSyntaxProof (jobRename)
open OriginalContextInsertionSyntaxProof (lengthRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Runtime FramedContentDefinitions FramedContentInductionDefinitions FramedContentInductionSyntax
open InternalApplicationStepPeelSupportProof (andLeft andRight)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atSize (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight jobs size : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowContent R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph size jobs))) :
 Nonempty (Derivation body Delta (AllFramedContent R job)) := by
 have hall := FramedContentDependencyProof.allDependencies R H M W c B job weight jobs size hb hj hw he hl
 apply FramedContentBindingProof.allIntro R job
 intro beta j Theta count value hinc hf
 have hj' := renameInto hj j Theta hinc
 have he' := renameInto he j Theta hinc
 have hl' := renameInto hl j Theta hinc
 have hall' := renameInto hall j Theta hinc
 simp only [jobRename,graph1Rename,lengthRename,InternalRecursionGraphStepSyntaxProof.conjunctionRename,
   VisitListCompletionSyntax.allRename,ContentVisitsSyntax.allRename] at hj' he' hl' hall'
 exact FramedContentLocalProof.actualLocalContent R H M W (c.relabel j) (B.relabel j) (job.relabel j)
   (jobs.relabel j) (size.relabel j) count value hj' he' hl' (andLeft hall') (andRight hall') hf
theorem atExpansion (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight jobs : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowContent R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 : Nonempty (Derivation body Delta (AllFramedContent R job)) := by
 apply programCases OriginalContextInsertion.length (Fin.cons jobs Fin.elim0) _
 intro beta j Theta size hi hq
 simp only [consTermRename,emptyRename] at hq
 rw [FramedContentSyntax.allContentRename]
 have hb' := renameInto hb j Theta hi
 have hj' := renameInto hj j Theta hi
 have hw' := renameInto hw j Theta hi
 have he' := renameInto he j Theta hi
 simp only [belowRename,jobRename,graph1Rename] at hb' hj' hw' he'
 exact atSize R H M W (c.relabel j) (B.relabel j) (job.relabel j) (weight.relabel j)
   (jobs.relabel j) size hb' hj' hw' he' hq
theorem atWeight (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowContent R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 : Nonempty (Derivation body Delta (AllFramedContent R job)) := by
 apply programCases OriginalHereditaryAnnotatedExpansion.expansion (Fin.cons job Fin.elim0) _
 intro beta j Theta jobs hi hq
 simp only [consTermRename,emptyRename] at hq
 rw [FramedContentSyntax.allContentRename]
 have hb' := renameInto hb j Theta hi
 have hj' := renameInto hj j Theta hi
 have hw' := renameInto hw j Theta hi
 simp only [belowRename,jobRename,graph1Rename] at hb' hj' hw'
 exact atExpansion R H M W (c.relabel j) (B.relabel j) (job.relabel j) (weight.relabel j) jobs hb' hj' hw' hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentAtWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.FramedContentAtWeightProof
