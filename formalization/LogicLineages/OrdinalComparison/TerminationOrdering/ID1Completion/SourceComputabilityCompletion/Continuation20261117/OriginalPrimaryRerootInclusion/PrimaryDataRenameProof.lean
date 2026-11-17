module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.PrimaryDataDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.PrimaryDataRenameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114
open TwoSol20261113.CalibratedPrimary.Membership
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalBetaTotalityProof (disjunctionElimination)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open PrimaryMonotonicity.InclusionProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

def rename {alpha beta : Type} {T P : Program 2} {E : Program 3}
    {body : Positive (Fin 1)} {Delta : List (Formula alpha)} {seed parameter sourceOut candidate targetOut sourcePool targetPool : OTerm alpha}
    (d : PrimaryData T P E body Delta seed parameter sourceOut candidate targetOut sourcePool targetPool)
    (j : alpha → beta) (Theta : List (Formula beta)) (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) :
    PrimaryData T P E body Theta (seed.relabel j) (parameter.relabel j) (sourceOut.relabel j) (candidate.relabel j) (targetOut.relabel j) (sourcePool.relabel j) (targetPool.relabel j) where
  sourceAdmitted := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] using renameInto d.sourceAdmitted j Theta hj
  targetAdmitted := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] using renameInto d.targetAdmitted j Theta hj
  sourcePoolGraph := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] using renameInto d.sourcePoolGraph j Theta hj
  targetPoolGraph := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] using renameInto d.targetPoolGraph j Theta hj
  sourcePrimary := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] using renameInto d.sourcePrimary j Theta hj
  targetPrimary := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] using renameInto d.targetPrimary j Theta hj
  member := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] using renameInto d.member j Theta hj
  pools := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename,includedRename] using renameInto d.pools j Theta hj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.PrimaryDataRenameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.PrimaryDataRenameProof
