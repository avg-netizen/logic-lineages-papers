module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnListFrameProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnListQueries
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
theorem nilCompletion (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced first second row rawPayload : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 6) rawPayload)))
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
 have htag' := renameInto htag j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at hj' ht' hr' hc' hp' hf' htag'
 have hs' := supplierRename j Theta children deletions produced first second row hi hs
 exact completionIntro R (frame.relabel j) (produced.relabel j) (numeral 0)
   (UniformReturnListFrameProof.nilFrame R (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) packed (rawPayload.relabel j)
     hj' ht' hr' hc' hp' hf' hq htag' hs')
theorem consWithValue (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced first second row rawPayload packed : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)))
 (hpacked : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing packed typ raw)))
 (hs : Supplier body Delta children deletions produced first second row) :
 Nonempty (Derivation body Delta (UniformReturnDefinitions.Completion R frame produced)) := by
 apply programCases OriginalHereditaryReturn.returnArgumentsCons (Fin.cons raw (Fin.cons first (Fin.cons second Fin.elim0))) _
 intro beta j Theta value hi hq
 rw [completionRename]
 simp only [consTermRename,emptyRename] at hq
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hc' := renameInto hc j Theta hi
 have hp' := renameInto hp j Theta hi
 have hf' := renameInto hf j Theta hi
 have htag' := renameInto htag j Theta hi
 have hpacked' := renameInto hpacked j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at hj' ht' hr' hc' hp' hf' htag' hpacked'
 have hs' := supplierRename j Theta children deletions produced first second row hi hs
 exact completionIntro R (frame.relabel j) (produced.relabel j) value
   (UniformReturnListFrameProof.consFrame R (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) (packed.relabel j) (rawPayload.relabel j) value
     hj' ht' hr' hc' hp' hf' hpacked' htag' hq hs')
theorem consCompletion (R : Program 2)
 (job typed typ rawJob raw parameter children deletions counts payload frame produced first second row rawPayload : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job (numeral 1) typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hf : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 1) payload)))
 (htag : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing raw (numeral 7) rawPayload)))
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
 have htag' := renameInto htag j Theta hi
 simp only [graph2Rename,graph3Rename,numeralRename] at hj' ht' hr' hc' hp' hf' htag'
 have hs' := supplierRename j Theta children deletions produced first second row hi hs
 exact consWithValue R (job.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (frame.relabel j) (produced.relabel j) (first.relabel j) (second.relabel j) (row.relabel j) (rawPayload.relabel j) packed
   hj' ht' hr' hc' hp' hf' htag' hq hs'
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnListQueries
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.UniformReturnListQueries
