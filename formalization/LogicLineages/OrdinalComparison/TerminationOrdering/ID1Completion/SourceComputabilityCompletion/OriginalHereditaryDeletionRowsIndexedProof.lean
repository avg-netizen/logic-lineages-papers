module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedProof
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
open OriginalHereditaryDeletionRows OriginalHereditaryDeletionRowsIndexedSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open OriginalHereditaryDeletionRowsIndexedCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow (Q : Program 2) : Nonempty (Derivation body Delta (row Q z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 5 Delta
  let input : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let parameter : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let output : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let cutoff : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let value : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let A := fields Q z input parameter output cutoff value
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    Q input parameter output cutoff value ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (Q : Program 2) (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row Q count))) :
    Nonempty (Derivation body Delta (row Q (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 5 Delta
  let input : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let parameter : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let output : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let cutoff : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let value : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
  let A := fields Q (suc c) input parameter output cutoff value
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore Q c input parameter output cutoff value hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (Q : Program 2) (count : OTerm alpha) : Nonempty (Derivation body Delta (row Q count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row Q (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) Q)
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      Q (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem actualIndexed : OriginalHereditaryDeletionRowsTargets.Indexed := by
  intro Q body alpha Delta count input parameter output cutoff value
  let A := fields Q count input parameter output cutoff value
  obtain ⟨h⟩ := rowApply (body := body) (Delta := A :: Delta) Q count input parameter output cutoff value
    (allRows Q count) ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsIndexedProof
