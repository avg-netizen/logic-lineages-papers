module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTermFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTermQueries
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalControlGraphSupportProof
open InternalAcceptanceSupportProof (programCases)
open InternalRecursionGraphStepSyntaxProof (consTermRename)
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open UniformReturnSupplierProof
open UniformReturnCompletionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem withValue (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced first second row packed root returned tail : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hroot : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)))
 (hreturned : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned packed first second)))
 (htail : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing tail returned row)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R frame produced)) := by
 apply programCases InternalPairing.pairing (Fin.cons root (Fin.cons tail Fin.elim0)) _
 intro beta j Theta value hi hq
 rw [completionRename]
 simp only [consTermRename,emptyRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 have hpacked' := renameInto hpacked j Theta hi
 have hroot' := renameInto hroot j Theta hi
 have hreturned' := renameInto hreturned j Theta hi
 have htail' := renameInto htail j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at hj' ht' hr' hc' hp' hf' hpacked' hroot' hreturned' htail'
 have hs' := supplierRename j Theta children deletions produced first second row hi hs
 exact completionIntro R (frame.relabel j) (produced.relabel j) value
   (UniformReturnTermFrameProof.termFrame R (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) (packed.relabel j) (root.relabel j) (returned.relabel j) (tail.relabel j) value
     hj' ht' hr' hc' hp' hf' hpacked' hroot' hreturned' htail' hq hs')
theorem withTail (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced first second row packed root returned : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hroot : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)))
 (hreturned : Nonempty (Derivation body Delta (graph3 OriginalHereditaryReturn.returnRoot returned packed first second)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R frame produced)) := by
 apply programCases InternalPairing.pairing (Fin.cons returned (Fin.cons row Fin.elim0)) _
 intro beta j Theta tail hi hq
 rw [completionRename]
 simp only [consTermRename,emptyRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 have hpacked' := renameInto hpacked j Theta hi
 have hroot' := renameInto hroot j Theta hi
 have hreturned' := renameInto hreturned j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at hj' ht' hr' hc' hp' hf' hpacked' hroot' hreturned'
 have hs' := supplierRename j Theta children deletions produced first second row hi hs
 exact withValue R (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) (packed.relabel j) (root.relabel j) (returned.relabel j) tail
   hj' ht' hr' hc' hp' hf' hpacked' hroot' hreturned' hq hs'
theorem withReturned (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced first second row packed root : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hroot : Nonempty (Derivation body Delta (graph2 (OriginalRootObservation.rootObservation R) root packed parameter)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R frame produced)) := by
 apply programCases OriginalHereditaryReturn.returnRoot (Fin.cons packed (Fin.cons first (Fin.cons second Fin.elim0))) _
 intro beta j Theta returned hi hq
 rw [completionRename]
 simp only [consTermRename,emptyRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 have hpacked' := renameInto hpacked j Theta hi
 have hroot' := renameInto hroot j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at hj' ht' hr' hc' hp' hf' hpacked' hroot'
 have hs' := supplierRename j Theta children deletions produced first second row hi hs
 exact withTail R (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) (packed.relabel j) (root.relabel j) returned
   hj' ht' hr' hc' hp' hf' hpacked' hroot' hq hs'
theorem withRoot (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced first second row packed : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R frame produced)) := by
 apply programCases (OriginalRootObservation.rootObservation R) (Fin.cons packed (Fin.cons parameter Fin.elim0)) _
 intro beta j Theta root hi hq
 rw [completionRename]
 simp only [consTermRename,emptyRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 have hpacked' := renameInto hpacked j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at hj' ht' hr' hc' hp' hf' hpacked'
 have hs' := supplierRename j Theta children deletions produced first second row hi hs
 exact withReturned R (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) (packed.relabel j) root
   hj' ht' hr' hc' hp' hf' hpacked' hq hs'
theorem termCompletion (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced first second row : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 0) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R frame produced)) := by
 apply programCases InternalPairing.pairing (Fin.cons typ (Fin.cons raw Fin.elim0)) _
 intro beta j Theta packed hi hq
 rw [completionRename]
 simp only [consTermRename,emptyRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at hj' ht' hr' hc' hp' hf'
 have hs' := supplierRename j Theta children deletions produced first second row hi hs
 exact withRoot R (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) packed
   hj' ht' hr' hc' hp' hf' hq hs'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTermQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnTermQueries
