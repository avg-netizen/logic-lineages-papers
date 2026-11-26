module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.PersistenceSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeDecoderTable.SupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open Continuation20261115.OriginalCodeDecoderTable Continuation20261115.OriginalCodeValidityGuard.PersistenceSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open Continuation20261115.OriginalCodeValidityGuard.CoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow (n : Nat) : Nonempty (Derivation body Delta (row n z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let bound : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let previous : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let next : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let index : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := fields n z bound previous next index
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    n bound previous next index ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (n : Nat) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row n count))) :
    Nonempty (Derivation body Delta (row n (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let bound : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let previous : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let next : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let index : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let A := fields n (suc c) bound previous next index
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
  have hrow' := InternalGraphCompositionFunctionalityProof.renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore n c bound previous next index hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (n : Nat) (count : OTerm alpha) : Nonempty (Derivation body Delta (row n count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row n (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) n)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      n (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem internalTablePersistence : Targets.InternalTablePersistence := by
  intro n body alpha Delta fuel bound previous next index hp hn hb hl
  exact rowApply n fuel bound previous next index (allRows n fuel)
    (andIntro (andIntro hp hn) (andIntro hb hl))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalCodeValidityGuard.Proof
