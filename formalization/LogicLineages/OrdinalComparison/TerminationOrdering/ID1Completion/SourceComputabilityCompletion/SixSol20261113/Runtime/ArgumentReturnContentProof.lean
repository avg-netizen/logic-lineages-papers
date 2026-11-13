module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnContentTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnGeometryProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ExpansionMapGeometryProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnContentProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
attribute [local irreducible] programGraph
theorem actualArgumentReturnContent : ArgumentReturnContentTargets.ActualArgumentReturnContent := by
 intro R Q H M W body alpha Delta job typed rawJob raw parameter gamma c children deletions counts payload frame jobs forward produced value hj ht hr hparameter ha harity hgamma hc hp hframe he hm hrev hf
 apply ExpansionMapGeometryProof.actualPartition
   (SixSol20261113.Context.ChildContentDefinitions.observationFromJob Q) body alpha Delta
   job (numeral 1) (numeral 0) typed rawJob raw parameter c gamma children deletions jobs forward produced _
   hj ht hr hparameter harity hgamma he hm hrev
 intro beta j Theta rawJobs annotatedPrefix childRow backwardChildren deletionPrefix hi hg
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have ha' := renameInto ha j Theta hi
 have harity' := renameInto harity j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hframe' := renameInto hframe j Theta hi
 have hf' := renameInto hf j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalInternalJobAdmissibleTransportSyntaxProof.admissibleRename,UniformReturnSyntax.frameRename] at hj' ht' hr' ha' harity' hc' hp' hframe' hf'
 simp only [numeralRename] at hg
 rw [graph1Rename]
 exact ArgumentReturnGeometryProof.fromGeometry R Q H M W (job.relabel j) (typed.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (gamma.relabel j) (c.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (value.relabel j) rawJobs annotatedPrefix childRow backwardChildren deletionPrefix hj' ht' hr' ha' harity' hc' hp' hframe' hf' hg
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnContentProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.ArgumentReturnContentProof
