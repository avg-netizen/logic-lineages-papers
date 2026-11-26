module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

/-- Keep the Program opaque during proof-context renaming. -/
theorem unaryRename (p : Program 1) (out input : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph1 p out input)))
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    Nonempty (Derivation body Theta (graph1 p (out.relabel j) (input.relabel j))) := by
  simpa only [graph1Rename] using
    InternalGraphCompositionFunctionalityProof.renameInto h j Theta hj

theorem binaryRename (p : Program 2) (out x y : OTerm alpha)
    (h : Nonempty (Derivation body Delta (graph2 p out x y)))
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta))
    (hj : ∀ q ∈ Delta, q.relabel j ∈ Theta) :
    Nonempty (Derivation body Theta (graph2 p (out.relabel j) (x.relabel j) (y.relabel j))) := by
  simpa only [graph2Rename] using
    InternalGraphCompositionFunctionalityProof.renameInto h j Theta hj

/-- Normalize only the finite tuple, without unfolding the queried Program. -/
theorem queryOneRename (p : Program 1) (input : OTerm alpha)
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta)) (out : OTerm beta)
    (h : Nonempty (Derivation body Theta
      (InternalGraphComposition.graph (OrdinaryArithmetic.graphFormula p) out
        (fun i => Term.relabel j ((Fin.cons input Fin.elim0 : Fin 1 → OTerm alpha) i))))) :
    Nonempty (Derivation body Theta (graph1 p out (input.relabel j))) := by
  simpa only [graph1,programGraph,consTermRename,emptyRename] using h

theorem queryTwoRename (p : Program 2) (x y : OTerm alpha)
    {beta : Type} (j : alpha → beta) (Theta : List (Formula beta)) (out : OTerm beta)
    (h : Nonempty (Derivation body Theta
      (InternalGraphComposition.graph (OrdinaryArithmetic.graphFormula p) out
        (fun i => Term.relabel j ((Fin.cons x (Fin.cons y Fin.elim0) : Fin 2 → OTerm alpha) i))))) :
    Nonempty (Derivation body Theta
      (programGraph p out (Fin.cons (x.relabel j) (Fin.cons (y.relabel j) Fin.elim0)))) := by
  simpa only [programGraph,consTermRename,emptyRename] using h

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSyntaxProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportInternalSyntaxProof
