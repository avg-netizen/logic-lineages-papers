module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof
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
open OriginalAllPositionContextDeleteInductionSyntaxProof OriginalAllPositionContextDeleteInductionCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroCore (count gamma deleted d : OTerm alpha)
    (hf : Nonempty (Derivation body Delta (fields count gamma z deleted d))) :
    Nonempty (Derivation body Delta (Insert d z deleted gamma)) := by
  apply nonzeroCases gamma _ (contextNonzero count gamma z (andLeft hf) (andLeft (andRight hf)))
  intro beta j Theta head tail hj hc
  simp only [insertRename,zRelabel]
  have hf' := renameInto hf j Theta hj
  simp only [fieldsRename,zRelabel] at hf'
  exact zeroAtCons (count.relabel j) (gamma.relabel j) head tail (deleted.relabel j) (d.relabel j) hc hf'

theorem succCore (count gamma cutoff deleted d : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row cutoff)))
    (hf : Nonempty (Derivation body Delta (fields count gamma (suc cutoff) deleted d))) :
    Nonempty (Derivation body Delta (Insert d (suc cutoff) deleted gamma)) := by
  apply nonzeroCases gamma _ (contextNonzero count gamma (suc cutoff) (andLeft hf) (andLeft (andRight hf)))
  intro beta j Theta head tail hj hc
  simp only [insertRename,sucRelabel]
  have hf' := renameInto hf j Theta hj
  simp only [fieldsRename,sucRelabel] at hf'
  have hrow' := renameInto hrow j Theta hj
  rw [rowRename] at hrow'
  exact successorAtCons (count.relabel j) (gamma.relabel j) (cutoff.relabel j) head tail
    (deleted.relabel j) (d.relabel j) hrow' hc hf'

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let count : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let gamma : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let deleted : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let d : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := fields count gamma z deleted d
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    count gamma deleted d ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (cutoff : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row cutoff))) :
    Nonempty (Derivation body Delta (row (suc cutoff))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let count : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let gamma : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let deleted : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let d : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let c := cutoff.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let A := fields count gamma (suc c) deleted d
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := succCore count gamma c deleted d hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (cutoff : OTerm alpha) : Nonempty (Derivation body Delta (row cutoff)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb cutoff) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem actualDeletionInsertion : OriginalAllPositionContextDeleteTargets.ActualDeletionInsertion := by
  intro body alpha Delta count gamma cutoff deleted d
  let A := fields count gamma cutoff deleted d
  obtain ⟨h⟩ := rowApply (body := body) (Delta := A :: Delta) count gamma cutoff deleted d (allRows cutoff)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.implicationIntroduction h⟩

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof
#print axioms LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteInductionProof.actualDeletionInsertion
