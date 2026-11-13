module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedAllChildrenProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedLocalQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedAtWeightProof
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
open SourceFramedDefinitions SourceFramedSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem atExpansion (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight jobs : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowCompletion R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 apply programCases OriginalContextInsertion.length (Fin.cons jobs Fin.elim0) _
 intro beta j Theta size hi hq
 simp only [consTermRename,emptyRename] at hq
 rw [JobCompletionSyntax.completionRename]
 have hb' := renameInto hb j Theta hi
 have hj' := renameInto hj j Theta hi
 have hw' := renameInto hw j Theta hi
 have he' := renameInto he j Theta hi
 simp only [belowRename,jobRename,graph1Rename] at hb' hj' hw' he'
 have hall := SourceFramedAllChildrenProof.allChildren R H M W
   (c.relabel j) (B.relabel j) (job.relabel j) (weight.relabel j) (jobs.relabel j) size hb' hj' hw' he' hq
 exact SourceFramedLocalQueries.actualLocalCompletion R H M W body beta Theta
   (c.relabel j) (B.relabel j) (job.relabel j) (jobs.relabel j) size hj' he' hq hall
theorem atWeight (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B job weight : OTerm alpha)
 (hb : Nonempty (Derivation body Delta (BelowCompletion R H M W c B weight)))
 (hj : Nonempty (Derivation body Delta (OriginalHereditaryInternalAgenda.Job H M W c B job)))
 (hw : Nonempty (Derivation body Delta (graph1 OriginalHereditaryFuelProgram.weight weight job)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Completion R job)) := by
 apply programCases OriginalHereditaryAnnotatedExpansion.expansion (Fin.cons job Fin.elim0) _
 intro beta j Theta jobs hi hq
 simp only [consTermRename,emptyRename] at hq
 rw [JobCompletionSyntax.completionRename]
 have hb' := renameInto hb j Theta hi
 have hj' := renameInto hj j Theta hi
 have hw' := renameInto hw j Theta hi
 simp only [belowRename,jobRename,graph1Rename] at hb' hj' hw'
 exact atExpansion R H M W (c.relabel j) (B.relabel j) (job.relabel j) (weight.relabel j) jobs hb' hj' hw' hq
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedAtWeightProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedAtWeightProof
