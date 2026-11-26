module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionQueries
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalAdditionLawsProof (add)
open InternalOriginalOrderSyntaxProof (addRelabel)
open PrefixFrameDefinitions PrefixFrameSyntax

theorem actualConcatenation : PrefixFrameTargets.ActualConcatenation := by
 intro R body alpha Delta first second firstCount secondCount firstRow secondRow agendaPrefix produced hf hs hp hr
 unfold PrefixFrame
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 unfold frameBody
 simp only [addRelabel]
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
 have hs' := renameInto hs Sum.inl Theta hinc
 have hp' := renameInto hp Sum.inl Theta hinc
 have hr' := renameInto hr Sum.inl Theta hinc
 simp only [frameRename,graph2Rename] at hf' hs' hp' hr'
 obtain ⟨h⟩ := PrefixFrameCompositionQueries.withWork R
   (first.relabel Sum.inl) (second.relabel Sum.inl) (firstCount.relabel Sum.inl) (secondCount.relabel Sum.inl)
   (firstRow.relabel Sum.inl) (secondRow.relabel Sum.inl) (agendaPrefix.relabel Sum.inl) (produced.relabel Sum.inl)
   suffix old work input joined output hf' hs' hp' hr' ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.PrefixFrameCompositionProof
