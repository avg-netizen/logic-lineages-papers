module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowSyntaxProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowBindingProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalContextInsertion OriginalContextInsertionSyntaxProof
open OriginalClassContextAllPositionObserver (deleteAt)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open OriginalHereditaryInternalAgenda
open OriginalInternalJobAdmissibleTransportSyntaxProof (admissibleSubst)
open OriginalTypedDecoderInternalLogicSyntaxProof (orSubst numeralSubst)
open InternalFiniteBlocks (block)
open OriginalHereditaryInternalAgendaSyntaxProof
open OriginalHereditaryInternalJobRow OriginalHereditaryInternalJobRowSyntaxProof
theorem jobsApply (H : Program 1) (M W : Program 2) (c B work count index frame : OTerm alpha)
 (h : Nonempty (Derivation body Delta (Jobs H M W c B work)))
 (hf : Nonempty (Derivation body Delta (lookupFields work count index frame))) :
 Nonempty (Derivation body Delta (Job H M W c B frame)) := by
 have hh := InternalClosedProgramsBindingProof.actualFiniteUniversalElimination body alpha 3 Delta
  (jobsMatrix H M W c B work) (fun i => emb (![count,index,frame] i)) h
 rw [jobsWitness] at hh
 obtain ⟨hh⟩ := hh
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination hh hf⟩

theorem jobsIntro (H : Program 1) (M W : Program 2) (c B work : OTerm alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count index frame : OTerm beta),
  (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (lookupFields (work.relabel j) count index frame)) →
  Nonempty (Derivation body Theta (Job H M W (c.relabel j) (B.relabel j) frame))) :
 Nonempty (Derivation body Delta (Jobs H M W c B work)) := by
 unfold Jobs
 apply InternalClosedProgramsBindingProof.actualFiniteUniversalIntroduction body alpha 3 Delta
 let count : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
 let index : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
 let frame : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
 let A := lookupFields (work.relabel Sum.inl) count index frame
 let Theta := A :: Delta.map (fun f => f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
 have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 3) ∈ Theta := by
  intro f hf
  exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 obtain ⟨h⟩ := next (alpha ⊕ Fin 3) Sum.inl Theta count index frame inc ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalJobRowBindingProof
