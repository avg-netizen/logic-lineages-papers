module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorErasureObservationProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Query the literal cell metadata and BOTH erased parent values. No returned
cell value, source acceptance, equality or native decoding is presumed. -/
theorem actualCases (left right gamma c cutoff : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (d deleted parameter erasedLeft erasedRight : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.lookup d (cutoff.relabel j) (gamma.relabel j))) →
   Nonempty (Derivation body Theta (graph2 OriginalClassContextAllPositionObserver.deleteAt deleted (cutoff.relabel j) (gamma.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing parameter (c.relabel j) deleted)) →
   Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedLeft d (cutoff.relabel j) (left.relabel j))) →
   Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedRight d (cutoff.relabel j) (right.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let look : Program 5 := .composition InternalRawListRecursion.lookup ![.projection 4,.projection 2]
 let del : Program 5 := .composition OriginalClassContextAllPositionObserver.deleteAt ![.projection 4,.projection 2]
 let par : Program 5 := pairOf (.projection 3) del
 let el : Program 5 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![look,.projection 4,.projection 0]
 let er : Program 5 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![look,.projection 4,.projection 1]
 let qs : Fin 5 → Program 5 := ![look,del,par,el,er]
 apply programsCases qs (Fin.cons left (Fin.cons right (Fin.cons gamma (Fin.cons c (Fin.cons cutoff Fin.elim0))))) psi
 intro beta j Theta ys hj hq
 simp only [consTermRename,emptyRename] at hq
 let xs : Fin 5 → OTerm beta := Fin.cons (left.relabel j) (Fin.cons (right.relabel j)
   (Fin.cons (gamma.relabel j) (Fin.cons (c.relabel j) (Fin.cons (cutoff.relabel j) Fin.elim0))))
 have hk := binaryRecover InternalRawListRecursion.lookup (.projection 4) (.projection 2)
   (ys 0) (cutoff.relabel j) (gamma.relabel j) xs (hq 0) (projectionValue 4 xs) (projectionValue 2 xs)
 have hd := binaryRecover OriginalClassContextAllPositionObserver.deleteAt (.projection 4) (.projection 2)
   (ys 1) (cutoff.relabel j) (gamma.relabel j) xs (hq 1) (projectionValue 4 xs) (projectionValue 2 xs)
 have hp := binaryRecover InternalPairing.pairing (.projection 3) del
   (ys 2) (c.relabel j) (ys 1) xs (hq 2) (projectionValue 3 xs) (hq 1)
 have hl := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw look (.projection 4) (.projection 0)
   (ys 3) (ys 0) (cutoff.relabel j) (left.relabel j) xs (hq 3) (hq 0) (projectionValue 4 xs) (projectionValue 0 xs)
 have hr := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw look (.projection 4) (.projection 1)
   (ys 4) (ys 0) (cutoff.relabel j) (right.relabel j) xs (hq 4) (hq 0) (projectionValue 4 xs) (projectionValue 1 xs)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj hk hd hp hl hr
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellQueries
