module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorCellQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorDefinitions
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSupportProof
open InternalApplicationCertificateConstructorsSyntaxProof InternalControlGraphSupportProof
open InternalRecursionGraphStepSyntaxProof
open OriginalRawSyntaxTransportInternalParserSupportProof (programsCases)
open InternalOriginalUniformVertexPathSupportProof (ternaryRecover)
open InternalTagArithmeticSyntaxProof (suc)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem actualCases (d cutoff childLeft childRight domain c deleted codomain : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (erasedChildLeft erasedChildRight childDeleted childParameter arrow : OTerm beta),
   (∀ q ∈ Delta, q.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedChildLeft (d.relabel j) (suc (cutoff.relabel j)) (childLeft.relabel j))) →
   Nonempty (Derivation body Theta (graph3 OriginalRawSyntaxTransport.erasePackedRaw erasedChildRight (d.relabel j) (suc (cutoff.relabel j)) (childRight.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalListCodec.consCode childDeleted (domain.relabel j) (deleted.relabel j))) →
   Nonempty (Derivation body Theta (graph2 InternalPairing.pairing childParameter (c.relabel j) childDeleted)) →
   Nonempty (Derivation body Theta (graph2 OriginalLambdaConstructor.arrow arrow (domain.relabel j) (codomain.relabel j))) →
   Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let nextCut : Program 8 := .composition .succ ![.projection 1]
 let el : Program 8 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![.projection 0,nextCut,.projection 2]
 let er : Program 8 := .composition OriginalRawSyntaxTransport.erasePackedRaw ![.projection 0,nextCut,.projection 3]
 let ctx : Program 8 := .composition InternalListCodec.consCode ![.projection 4,.projection 6]
 let par : Program 8 := pairOf (.projection 5) ctx
 let arr : Program 8 := .composition OriginalLambdaConstructor.arrow ![.projection 4,.projection 7]
 let qs : Fin 5 → Program 8 := ![el,er,ctx,par,arr]
 let xs : Fin 8 → OTerm alpha := ![d,cutoff,childLeft,childRight,domain,c,deleted,codomain]
 apply programsCases qs xs psi
 intro beta j Theta ys hj hq
 let xx : Fin 8 → OTerm beta := fun i => (xs i).relabel j
 have hcut := unaryValue Program.succ (.projection 1) (suc (cutoff.relabel j)) (cutoff.relabel j) xx
   (InternalControlGraphSupportProof.successorValue (Fin.cons (cutoff.relabel j) Fin.elim0)) (projectionValue 1 xx)
 have hl := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 0) nextCut (.projection 2)
   (ys 0) (d.relabel j) (suc (cutoff.relabel j)) (childLeft.relabel j) xx (hq 0) (projectionValue 0 xx) hcut (projectionValue 2 xx)
 have hr := ternaryRecover OriginalRawSyntaxTransport.erasePackedRaw (.projection 0) nextCut (.projection 3)
   (ys 1) (d.relabel j) (suc (cutoff.relabel j)) (childRight.relabel j) xx (hq 1) (projectionValue 0 xx) hcut (projectionValue 3 xx)
 have hc := binaryRecover InternalListCodec.consCode (.projection 4) (.projection 6)
   (ys 2) (domain.relabel j) (deleted.relabel j) xx (hq 2) (projectionValue 4 xx) (projectionValue 6 xx)
 have hp := binaryRecover InternalPairing.pairing (.projection 5) ctx
   (ys 3) (c.relabel j) (ys 2) xx (hq 3) (projectionValue 5 xx) (hq 2)
 have ha := binaryRecover OriginalLambdaConstructor.arrow (.projection 4) (.projection 7)
   (ys 4) (domain.relabel j) (codomain.relabel j) xx (hq 4) (projectionValue 4 xx) (projectionValue 7 xx)
 exact next beta j Theta (ys 0) (ys 1) (ys 2) (ys 3) (ys 4) hj hl hr hc hp ha
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.EvaluatorConstructorLambdaCellQueries
