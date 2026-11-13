module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnShapeCompletion
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSourceCompletion
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformReturnSupplierProof
open UniformReturnCompletionSyntax (completionRename)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem fromAdmissible (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter gamma c children deletions counts payload frame produced first second row : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ha : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R frame produced)) := by
 let qs : Fin 2 → Program 1 := ![InternalUnpair.left,InternalUnpair.right]
 let xs : Fin 1 → OTerm alpha := Fin.cons raw Fin.elim0
 apply OriginalLambdaConstructorGraphSyntaxProof.queryCases qs xs _
 intro beta j ys Theta hi hq
 have hx : (fun i => (xs i).relabel j) = Fin.cons (raw.relabel j) Fin.elim0 := by
   funext i
   exact Fin.cases rfl (fun k => Fin.elim0 k) i
 rw [hx] at hq
 have hraw := reconstructPair (raw.relabel j) (ys 0) (ys 1) (hq 0) (hq 1)
 rw [completionRename]
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have ha' := renameInto ha j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 simp only [graph2Rename,numeralRename,admissibleRename] at hj' ht' hr' ha' hc' hp' hf'
 have hshape := OriginalInternalJobAdmissibleShapeProof.supportedReturn body H M W beta Theta
   (role.relabel j) (typ.relabel j) (raw.relabel j) (gamma.relabel j) (c.relabel j) (ys 0) (ys 1) ha' hraw
 have hs' := supplierRename j Theta children deletions produced first second row hi hs
 exact UniformReturnShapeCompletion.fromShape R
   (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) (ys 0) (ys 1)
   hj' ht' hr' hc' hp' hf' hraw hshape hs'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSourceCompletion
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSourceCompletion
