module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.RequestDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.RequestRenameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalControlGraphSupportProof InternalGraphCompositionFunctionalityProof
open InternalApplicationCertificateConstructorsSyntaxProof
open InternalTagArithmeticSyntaxProof (eqn eqnRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116

def rename {alpha beta : Type} {n : Nat} {arity : Fin n → Nat}
    {body : Positive (Fin 1)} {Delta : List (Formula alpha)}
    {seed parameter out candidate seedQ targetQ : OTerm alpha}
    (q : Request n arity body Delta seed parameter out candidate seedQ targetQ)
    (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ p ∈ Delta, p.relabel j ∈ Theta) :
    Request n arity body Theta (seed.relabel j) (parameter.relabel j) (out.relabel j)
      (candidate.relabel j) (seedQ.relabel j) (targetQ.relabel j) where
  admitted := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] using renameInto q.admitted j Theta hj
  primary := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] using renameInto q.primary j Theta hj
  member := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] using renameInto q.member j Theta hj
  sourceCandidates := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] using renameInto q.sourceCandidates j Theta hj
  targetCandidates := by simpa only [graph2Rename,GuardedSourceSyntaxProof.numeralRename] using renameInto q.targetCandidates j Theta hj
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.RequestRenameProof
