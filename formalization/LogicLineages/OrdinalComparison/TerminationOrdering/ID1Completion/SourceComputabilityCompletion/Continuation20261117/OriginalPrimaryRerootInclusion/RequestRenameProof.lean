module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.RequestDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.RequestRenameProof
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

def rename {alpha beta : Type} {n : Nat} {arity : Fin n → Nat}
    {body : Positive (Fin 1)} {Delta : List (Formula alpha)}
    {seed parameter typ raw context gamma types out candidate targetOut : OTerm alpha}
    (q : Request n arity body Delta seed parameter typ raw context gamma types out candidate targetOut) (j : alpha → beta)
    (Theta : List (Formula beta)) (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) :
    Request n arity body Theta (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (out.relabel j) (candidate.relabel j) (targetOut.relabel j) where
  seedPair := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.seedPair j Theta hj
  parameterPair := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.parameterPair j Theta hj
  guard := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.guard j Theta hj
  typesGraph := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.typesGraph j Theta hj
  closed := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.closed j Theta hj
  accepted := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.accepted j Theta hj
  primary := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.primary j Theta hj
  member := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.member j Theta hj
  targetPrimary := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.targetPrimary j Theta hj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.RequestRenameProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalPrimaryRerootInclusion.RequestRenameProof
