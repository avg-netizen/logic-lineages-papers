module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunCore
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedStateQueries
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobFrameSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open InternalTagArithmeticSyntaxProof (suc sucRelabel)
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem runAtGeometry (R : Program 2)
 (job role typed typ rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged count produced value suffix old visit work input pushed output : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)))
 (hprefix : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged count produced)))
 (hreturn : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R returnFrame produced value)))
 (hg : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.geometry job value suffix old visit work input pushed output))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R)
   output (suc (add count (suc (numeral 0)))) input)) := by
 apply SourceFramedStateQueries.stateCases returnFrame tagged produced suffix old _
 intro beta j Theta returnRest next visitOutput results returnInput hi hrest hnext hvisit hresults hinput
 simp only [graph2Rename,sucRelabel,addRelabel,numeralRename]
 have hj' := renameInto hj j Theta hi
 have ht' := renameInto ht j Theta hi
 have hr' := renameInto hr j Theta hi
 have hp' := renameInto hp j Theta hi
 have ha' := renameInto ha j Theta hi
 have hl' := renameInto hl j Theta hi
 have hc' := renameInto hc j Theta hi
 have hpay' := renameInto hpay j Theta hi
 have hframe' := renameInto hframe j Theta hi
 have he' := renameInto he j Theta hi
 have htag' := renameInto htag j Theta hi
 have hprefix' := renameInto hprefix j Theta hi
 have hreturn' := renameInto hreturn j Theta hi
 have hg' := renameInto hg j Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   PrefixFrameSyntax.frameRename,UniformReturnSyntax.frameRename,JobFrameSyntax.geometryRename] at hj' ht' hr' hp' ha' hl' hc' hpay' hframe' he' htag' hprefix' hreturn' hg'
 exact SourceFramedRunCore.runWithStates R (job.relabel j) (role.relabel j) (typed.relabel j) (typ.relabel j) (rawJob.relabel j) (raw.relabel j) (parameter.relabel j) (c.relabel j) (gamma.relabel j) (children.relabel j) (deletions.relabel j) (counts.relabel j) (payload.relabel j) (returnFrame.relabel j) (jobs.relabel j) (tagged.relabel j) (count.relabel j) (produced.relabel j) (value.relabel j) (input.relabel j) (work.relabel j) (old.relabel j) (visit.relabel j) (suffix.relabel j) returnRest next visitOutput results returnInput (pushed.relabel j) (output.relabel j)
   hj' ht' hr' hp' ha' hl' hc' hpay' hframe' he' htag' hprefix' hreturn' hg' hrest hnext hvisit hresults hinput
theorem framed (R : Program 2)
 (job role typed typ rawJob raw parameter c gamma children deletions counts payload returnFrame jobs tagged count produced value : OTerm alpha)
 (hj : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing job role typed)))
 (ht : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing typed typ rawJob)))
 (hr : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing rawJob raw parameter)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing parameter c gamma)))
 (ha : Nonempty (Derivation body Delta (graph1 (OriginalRawSyntaxTransport.arityOf (.projection 0)) children raw)))
 (hl : Nonempty (Derivation body Delta (OriginalContextInsertion.lengthGraph deletions gamma)))
 (hc : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing counts children deletions)))
 (hpay : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing payload job counts)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing returnFrame (numeral 1) payload)))
 (he : Nonempty (Derivation body Delta (graph1 OriginalHereditaryAnnotatedExpansion.expansion jobs job)))
 (htag : Nonempty (Derivation body Delta (graph1 OriginalHereditaryVisitScheduler.tagVisits tagged jobs)))
 (hprefix : Nonempty (Derivation body Delta (PrefixFrameDefinitions.PrefixFrame R tagged count produced)))
 (hreturn : Nonempty (Derivation body Delta (UniformReturnDefinitions.Framed R returnFrame produced value)))
 : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R
    job (suc (add count (suc (numeral 0)))) value)) := by
 unfold SixSol20261112.Runtime.FramedCompletionDefinitions.Framed
 apply actualFiniteUniversalIntroduction body alpha 7 Delta
 unfold SixSol20261112.Runtime.FramedCompletionDefinitions.framedBody
 simp only [sucRelabel,addRelabel,numeralRename]
 let suffix : OTerm (alpha ⊕ Fin 7) := .var (.inr 0)
 let old : OTerm (alpha ⊕ Fin 7) := .var (.inr 1)
 let visit : OTerm (alpha ⊕ Fin 7) := .var (.inr 2)
 let work : OTerm (alpha ⊕ Fin 7) := .var (.inr 3)
 let input : OTerm (alpha ⊕ Fin 7) := .var (.inr 4)
 let pushed : OTerm (alpha ⊕ Fin 7) := .var (.inr 5)
 let output : OTerm (alpha ⊕ Fin 7) := .var (.inr 6)
 let A := SixSol20261112.Runtime.FramedCompletionDefinitions.geometry
   (job.relabel Sum.inl) (value.relabel Sum.inl) suffix old visit work input pushed output
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 7))
 have hi : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 7) ∈ Theta :=
   fun f h => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,h,rfl⟩)
 have hj' := renameInto hj Sum.inl Theta hi
 have ht' := renameInto ht Sum.inl Theta hi
 have hr' := renameInto hr Sum.inl Theta hi
 have hp' := renameInto hp Sum.inl Theta hi
 have ha' := renameInto ha Sum.inl Theta hi
 have hl' := renameInto hl Sum.inl Theta hi
 have hc' := renameInto hc Sum.inl Theta hi
 have hpay' := renameInto hpay Sum.inl Theta hi
 have hframe' := renameInto hframe Sum.inl Theta hi
 have he' := renameInto he Sum.inl Theta hi
 have htag' := renameInto htag Sum.inl Theta hi
 have hprefix' := renameInto hprefix Sum.inl Theta hi
 have hreturn' := renameInto hreturn Sum.inl Theta hi
 simp only [graph1Rename,graph2Rename,numeralRename,OriginalContextInsertionSyntaxProof.lengthRename,
   PrefixFrameSyntax.frameRename,UniformReturnSyntax.frameRename] at hj' ht' hr' hp' ha' hl' hc' hpay' hframe' he' htag' hprefix' hreturn'
 obtain ⟨h⟩ := runAtGeometry R (job.relabel Sum.inl) (role.relabel Sum.inl) (typed.relabel Sum.inl) (typ.relabel Sum.inl) (rawJob.relabel Sum.inl) (raw.relabel Sum.inl) (parameter.relabel Sum.inl) (c.relabel Sum.inl) (gamma.relabel Sum.inl) (children.relabel Sum.inl) (deletions.relabel Sum.inl) (counts.relabel Sum.inl) (payload.relabel Sum.inl) (returnFrame.relabel Sum.inl) (jobs.relabel Sum.inl) (tagged.relabel Sum.inl) (count.relabel Sum.inl) (produced.relabel Sum.inl) (value.relabel Sum.inl) suffix old visit work input pushed output
   hj' ht' hr' hp' ha' hl' hc' hpay' hframe' he' htag' hprefix' hreturn' ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.SourceFramedRunProof
