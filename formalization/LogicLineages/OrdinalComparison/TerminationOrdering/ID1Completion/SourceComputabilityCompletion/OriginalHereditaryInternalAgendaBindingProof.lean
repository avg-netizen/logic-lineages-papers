module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalParameterizedNumericIterationPreservationProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaDivisionSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalJobAdmissibleTransportSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaSyntaxProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
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
theorem jobIntro (H : Program 1) (M W : Program 2) (c B job role typ typed rawJob raw parameter gamma weight : OTerm alpha)
 (h : Nonempty (Derivation body Delta (jobFields H M W c B job role typ typed rawJob raw parameter gamma weight))) :
 Nonempty (Derivation body Delta (Job H M W c B job)) := by
 have hi : Nonempty (Derivation body Delta ((jobMatrix H M W c B job).subst
   (Sum.elim Term.var (fun i => emb (![role,typ,typed,rawJob,raw,parameter,gamma,weight] i))))) := by
  rw [jobWitness]
  exact h
 exact InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 8 Delta (jobMatrix H M W c B job)
  (fun i => emb (![role,typ,typed,rawJob,raw,parameter,gamma,weight] i)) hi

theorem jobCases (H : Program 1) (M W : Program 2) (c B job : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (Job H M W c B job)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (role typ typed rawJob raw parameter gamma weight : OTerm beta),
  (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (jobFields H M W (c.relabel j) (B.relabel j) (job.relabel j) role typ typed rawJob raw parameter gamma weight)) →
  Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let P := jobMatrix H M W c B job
 apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 8 Delta P psi h
 exact next (alpha ⊕ Fin 8) Sum.inl (P :: Delta.map (fun f => f.relabel Sum.inl))
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2)) (.var (.inr 3)) (.var (.inr 4)) (.var (.inr 5)) (.var (.inr 6)) (.var (.inr 7))
  (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  ⟨Derivation.hypothesis List.mem_cons_self⟩
theorem frameIntro (H : Program 1) (M W : Program 2) (c B frame parent payload counts : OTerm alpha)
 (h : Nonempty (Derivation body Delta (frameFields H M W c B frame parent payload counts))) :
 Nonempty (Derivation body Delta (Frame H M W c B frame)) := by
 apply InternalFiniteBlocksProof.actualFiniteExistentialIntroduction body alpha 3 Delta _ (fun i => emb (![parent,payload,counts] i))
 rw [frameWitness]
 exact h

theorem frameCases (H : Program 1) (M W : Program 2) (c B frame : OTerm alpha) (psi : Formula alpha)
 (h : Nonempty (Derivation body Delta (Frame H M W c B frame)))
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (parent payload counts : OTerm beta),
  (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (frameFields H M W (c.relabel j) (B.relabel j) (frame.relabel j) parent payload counts)) →
  Nonempty (Derivation body Theta (psi.relabel j))) : Nonempty (Derivation body Delta psi) := by
 let P := frameMatrix H M W c B frame
 apply InternalFiniteBlocksProof.actualFiniteExistentialElimination body alpha 3 Delta P psi h
 exact next (alpha ⊕ Fin 3) Sum.inl (P :: Delta.map (fun f => f.relabel Sum.inl))
  (.var (.inr 0)) (.var (.inr 1)) (.var (.inr 2))
  (fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩))
  ⟨Derivation.hypothesis List.mem_cons_self⟩
theorem agendaApply (H : Program 1) (M W : Program 2) (c B work count index frame : OTerm alpha)
 (h : Nonempty (Derivation body Delta (Agenda H M W c B work)))
 (hf : Nonempty (Derivation body Delta (lookupFields work count index frame))) :
 Nonempty (Derivation body Delta (Frame H M W c B frame)) := by
 have hh := InternalClosedProgramsBindingProof.actualFiniteUniversalElimination body alpha 3 Delta
  (agendaMatrix H M W c B work) (fun i => emb (![count,index,frame] i)) h
 rw [agendaWitness] at hh
 obtain ⟨hh⟩ := hh
 obtain ⟨hf⟩ := hf
 exact ⟨Derivation.implicationElimination hh hf⟩

theorem agendaIntro (H : Program 1) (M W : Program 2) (c B work : OTerm alpha)
 (next : ∀ (beta : Type) (j : alpha → beta) (Theta : List (Formula beta)) (count index frame : OTerm beta),
  (∀ f ∈ Delta, f.relabel j ∈ Theta) →
  Nonempty (Derivation body Theta (lookupFields (work.relabel j) count index frame)) →
  Nonempty (Derivation body Theta (Frame H M W (c.relabel j) (B.relabel j) frame))) :
 Nonempty (Derivation body Delta (Agenda H M W c B work)) := by
 unfold Agenda
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
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryInternalAgendaBindingProof
