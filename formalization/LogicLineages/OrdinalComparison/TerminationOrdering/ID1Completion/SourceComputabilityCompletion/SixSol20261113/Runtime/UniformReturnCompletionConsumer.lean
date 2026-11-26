module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSourceCompletion
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnSupplierQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnCompletionConsumer
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open InternalTagArithmeticSupportProof (refl)
open InternalTagArithmeticSyntaxProof (z suc zRelabel sucRelabel)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleRename)
open InternalAdditionLawsProof (add)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformReturnCompletionSyntax (completionRename)
open UniformReturnShapeCompletion (weakenInto)
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem completionConsumer (R : Program 2) (H : Program 1) (M W : Program 2)
 (job role typed typ rawJob raw parameter gamma c children deletions counts payload frame produced : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (ha : Nonempty (Derivation body Delta (OriginalInternalJobAdmissible.Admissible H M W role typ raw gamma c)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 : UniformReturnSupplierQueries.Consumer body Delta children deletions produced
   (UniformReturnDefinitions.Completion R frame produced) := by
 intro beta j Theta first second row hi hs
 rw [completionRename]
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have ha' := renameInto ha j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 simp only [graph2Rename,numeralRename,admissibleRename] at hj' ht' hr' ha' hc' hp' hf'
 exact UniformReturnSourceCompletion.fromAdmissible R H M W
   (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (gamma.relabel j) (c.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) first second row
   hj' ht' hr' ha' hc' hp' hf' hs
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnCompletionConsumer
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnCompletionConsumer
