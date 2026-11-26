module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnStackProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.CountedPrefixProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportInternalParserSupportProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnPartitionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof (consTermRename conjunctionRename)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open InternalAdditionLawsProof (add)
open InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
/-- Actual bounded front/drop witnesses, obtained before choosing any old
background. They carry the deletion length and literal produced-row partition. -/
theorem partitionCases (children deletions produced : OTerm alpha) (psi : Formula alpha)
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph (add children deletions) produced)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (front childRow : OTerm beta),
   (∀ f ∈ Delta, f.relabel j ∈ Theta) →
   Nonempty (Derivation body Theta (OriginalContextInsertion.lengthGraph (deletions.relabel j) front)) →
   Nonempty (Derivation body Theta (OriginalContextInsertion.lengthGraph (children.relabel j) childRow)) →
   Nonempty (Derivation body Theta (graph2 InternalApplicationValidityStackAppend.append (produced.relabel j) front childRow)) →
   Nonempty (Derivation body Theta (psi.relabel j))) :
 Nonempty (Derivation body Delta psi) := by
 let qs : Fin 2 → Program 2 := ![OriginalClassContextAllPositionObserver.front,InternalRawListRecursion.drop]
 let xs : Fin 2 → OTerm alpha := ![deletions,produced]
 apply OriginalRawSyntaxTransportInternalParserSupportProof.programsCases qs xs psi
 intro beta j Theta ys hinc hq
 have hx : (fun a => (xs a).relabel j) =
   Fin.cons (deletions.relabel j) (Fin.cons (produced.relabel j) Fin.elim0) := by
   funext a
   exact Fin.cases rfl (fun k => Fin.cases rfl (fun l => Fin.elim0 l) k) a
 rw [hx] at hq
 have hfront : Nonempty (Derivation body Theta (graph2 OriginalClassContextAllPositionObserver.front (ys 0) (deletions.relabel j) (produced.relabel j))) := by
   simpa only [qs,xs,Matrix.cons_val_zero,Matrix.cons_val_one,graph2,
     OriginalRawSyntaxTransportInternalConstructorSupportProof.twoTuple] using hq (0 : Fin 2)
 have hdrop : Nonempty (Derivation body Theta (graph2 InternalRawListRecursion.drop (ys 1) (deletions.relabel j) (produced.relabel j))) := by
   simpa only [qs,xs,Matrix.cons_val_zero,Matrix.cons_val_one,graph2,
     OriginalRawSyntaxTransportInternalConstructorSupportProof.twoTuple] using hq (1 : Fin 2)
 have hl' := renameInto hl j Theta hinc
 simp only [OriginalContextInsertionSyntaxProof.lengthRename,InternalOriginalOrderSyntaxProof.addRelabel] at hl'
 have hlcomm := outputTransport OriginalContextInsertion.length
   (add (children.relabel j) (deletions.relabel j)) (add (deletions.relabel j) (children.relabel j))
   (Fin.cons (produced.relabel j) Fin.elim0)
   ⟨InternalAdditionCancellationProof.commutativity (children.relabel j) (deletions.relabel j)⟩ hl'
 have hp := SixSol20261112.Runtime.CountedPrefixProof.actualCountedSplit body beta Theta
   (deletions.relabel j) (children.relabel j) (produced.relabel j) (ys 0) (ys 1) hlcomm hfront hdrop
 exact next beta j Theta (ys 0) (ys 1) hinc (andLeft hp)
   (andLeft (andRight hp)) (andRight (andRight hp))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnPartitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnPartitionProof
