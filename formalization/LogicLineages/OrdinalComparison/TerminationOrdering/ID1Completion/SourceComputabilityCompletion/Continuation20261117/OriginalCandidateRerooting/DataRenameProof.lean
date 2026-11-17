module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.DataDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationCertificateConstructorsSyntaxProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.DataRenameProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open Continuation20261114 Continuation20261115 Continuation20261116
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open DataDefinitions

def rename {alpha beta : Type} {n : Nat} {arity : Fin n → Nat}
    {body : Positive (Fin 1)} {Delta : List (Formula alpha)}
    {seed candidate parameter : OTerm alpha}
    (d : Data n arity body Delta seed candidate parameter) (j : alpha → beta)
    (Theta : List (Formula beta)) (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    Data n arity body Theta (seed.relabel j) (candidate.relabel j) (parameter.relabel j) where
  root := d.root.relabel j
  left := d.left.relabel j
  right := d.right.relabel j
  bounds := d.bounds.relabel j
  sourcePair := by simpa only [graph2Rename] using renameInto d.sourcePair j Theta hj
  targetPair := by simpa only [graph2Rename] using renameInto d.targetPair j Theta hj
  sourceBounds := by simpa only [graph1Rename] using renameInto d.sourceBounds j Theta hj
  targetBounds := by simpa only [graph1Rename] using renameInto d.targetBounds j Theta hj
  sourceAdmitted := by simpa only [graph2Rename, GuardedSourceSyntaxProof.numeralRename] using renameInto d.sourceAdmitted j Theta hj
  targetAdmitted := by simpa only [graph2Rename, GuardedSourceSyntaxProof.numeralRename] using renameInto d.targetAdmitted j Theta hj

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalCandidateRerooting.DataRenameProof
