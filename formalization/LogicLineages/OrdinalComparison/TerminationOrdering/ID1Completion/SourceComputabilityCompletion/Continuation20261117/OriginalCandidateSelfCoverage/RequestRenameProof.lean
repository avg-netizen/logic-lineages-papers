module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.RequestDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.RequestRenameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalApplicationCertificateConstructorsSupportProof InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalTagArithmeticSyntaxProof (suc)
def rename {alpha beta : Type} {n : Nat} {arity : Fin n → Nat} {H : Program 1}
    {body : Positive (Fin 1)} {Delta : List (Formula alpha)}
    {seed parameter typ raw context gamma types out : OTerm alpha}
    (q : Request n arity H body Delta seed parameter typ raw context gamma types out)
    (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) :
    Request n arity H body Theta (seed.relabel j) (parameter.relabel j) (typ.relabel j) (raw.relabel j) (context.relabel j) (gamma.relabel j) (types.relabel j) (out.relabel j) where
  seedPair := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.seedPair j Theta hj
  parameterPair := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.parameterPair j Theta hj
  guard := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.guard j Theta hj
  typesGraph := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.typesGraph j Theta hj
  closed := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.closed j Theta hj
  accepted := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.accepted j Theta hj
  candidates := by simpa only [graph1Rename,graph2Rename,GuardedSourceSyntaxProof.numeralRename,WindowSourceHeadInclusion.ClosureSyntaxProof.closureRename,OriginalUniverseDecoderInternalAcceptanceSyntaxProof.termAcceptedRename] using renameInto q.candidates j Theta hj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateSelfCoverage.RequestRenameProof
