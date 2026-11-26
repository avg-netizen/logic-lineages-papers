module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameIdentityProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.JobFrameSyntax
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSingletonProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalGraphCompositionEqualityProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open SourceComputabilityFormulaSupportProof (numeral)
open GuardedSourceSyntaxProof (numeralRename)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open PrefixFrameDefinitions PrefixFrameSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem singletonCore (R : Program 2) (job count value frame agendaPrefix produced suffix old work input joined output : OTerm alpha)
 (hf : Nonempty (Derivation body Delta (SixSol20261112.Runtime.FramedCompletionDefinitions.Framed R job count value)))
 (hframe : Nonempty (Derivation body Delta (graph2 InternalPairing.pairing frame (numeral 0) job)))
 (hp : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode agendaPrefix frame (numeral 0))))
 (hr : Nonempty (Derivation body Delta (graph2 InternalListCodec.consCode produced value (numeral 0))))
 (hg : Nonempty (Derivation body Delta (geometry agendaPrefix produced suffix old work input joined output))) :
 Nonempty (Derivation body Delta (graph2 (OriginalHereditaryRuntimeIterationDefinitions.run R) output count input)) := by
 have hw := InternalApplicationValidityStackAppendListProof.consForward agendaPrefix frame (numeral 0) suffix suffix work
   hp (InternalApplicationValidityStackAppendListProof.appendZeroValue suffix) (andLeft hg)
 have hj := InternalApplicationValidityStackAppendListProof.consForward produced value (numeral 0) old old joined
   hr (InternalApplicationValidityStackAppendListProof.appendZeroValue old) (andLeft (andRight (andRight hg)))
 exact JobFrameSyntax.frameApply R job count value suffix old frame work input joined output hf
   (andIntro hframe (andIntro hw (andIntro (andLeft (andRight hg)) (andIntro hj (andRight (andRight (andRight hg)))))))

theorem actualSingleton : PrefixFrameTargets.ActualSingleton := by
 intro R body alpha Delta job count value frame agendaPrefix produced hf hframe hp hr
 unfold PrefixFrame
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 unfold frameBody
 let suffix : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let old : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let work : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let input : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let joined : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let output : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let A := geometry (agendaPrefix.relabel Sum.inl) (produced.relabel Sum.inl) suffix old work input joined output
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
 have hinc : ∀ p ∈ Delta, p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6) ∈ Theta := by
   intro p hp
   exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
 have hf' := renameInto hf Sum.inl Theta hinc
 have hframe' := renameInto hframe Sum.inl Theta hinc
 have hp' := renameInto hp Sum.inl Theta hinc
 have hr' := renameInto hr Sum.inl Theta hinc
 simp only [JobFrameSyntax.frameRename,graph2Rename,numeralRename] at hf' hframe' hp' hr'
 obtain ⟨h⟩ := singletonCore R (job.relabel Sum.inl) (count.relabel Sum.inl) (value.relabel Sum.inl)
   (frame.relabel Sum.inl) (agendaPrefix.relabel Sum.inl) (produced.relabel Sum.inl)
   suffix old work input joined output hf' hframe' hp' hr' ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSingletonProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameSingletonProof
