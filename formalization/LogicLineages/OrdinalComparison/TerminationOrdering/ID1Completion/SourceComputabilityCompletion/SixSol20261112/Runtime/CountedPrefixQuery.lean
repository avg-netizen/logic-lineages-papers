module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixSyntax
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaConstructorGraphSyntaxProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixQuery
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof (binaryRecover)
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem tailPieces (count tail head : OTerm alpha) (psi : Formula alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta))
   (front suffix candidate : OTerm beta), (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta
     (graph2 OriginalClassContextAllPositionObserver.front front (count.relabel j) (tail.relabel j))) →
   Nonempty (Derivation body Theta
     (graph2 InternalRawListRecursion.drop suffix (count.relabel j) (tail.relabel j))) →
   Nonempty (Derivation body Theta
     (graph2 InternalListCodec.consCode candidate (head.relabel j) front)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let takeP : Program 3 := .composition OriginalClassContextAllPositionObserver.front ![.projection 0,.projection 1]
 let dropP : Program 3 := .composition InternalRawListRecursion.drop ![.projection 0,.projection 1]
 let qs : Fin 3 → Program 3 := ![takeP,dropP,consOf (.projection 2) takeP]
 let xs : Fin 3 → OTerm alpha := Fin.cons count (Fin.cons tail (Fin.cons head Fin.elim0))
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs psi
 intro beta j ys Theta hinc hg
 simp only [xs,consTermRename,emptyRename] at hg
 let xx : Fin 3 → OTerm beta := Fin.cons (count.relabel j) (Fin.cons (tail.relabel j) (Fin.cons (head.relabel j) Fin.elim0))
 have ht : Nonempty (Derivation body Theta (programGraph takeP (ys 0) xx)) := by
   simpa only [qs,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons] using hg 0
 have hd : Nonempty (Derivation body Theta (programGraph dropP (ys 1) xx)) := by
   simpa only [qs,Matrix.cons_val_one,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons] using hg 1
 have hc : Nonempty (Derivation body Theta (programGraph (consOf (.projection 2) takeP) (ys 2) xx)) := by
   simpa only [qs,Matrix.cons_val_two,Matrix.cons_val_zero,Matrix.head_cons,Matrix.tail_cons] using hg 2
 have hfront := binaryRecover OriginalClassContextAllPositionObserver.front (.projection 0) (.projection 1)
   (ys 0) (count.relabel j) (tail.relabel j) xx ht (projectionValue 0 xx) (projectionValue 1 xx)
 have hdrop := binaryRecover InternalRawListRecursion.drop (.projection 0) (.projection 1)
   (ys 1) (count.relabel j) (tail.relabel j) xx hd (projectionValue 0 xx) (projectionValue 1 xx)
 have hcons := binaryRecover InternalListCodec.consCode (.projection 2) takeP
   (ys 2) (head.relabel j) (ys 0) xx hc (projectionValue 2 xx) ht
 exact next beta j Theta (ys 0) (ys 1) (ys 2) hinc hfront hdrop hcons
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixQuery
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixQuery
