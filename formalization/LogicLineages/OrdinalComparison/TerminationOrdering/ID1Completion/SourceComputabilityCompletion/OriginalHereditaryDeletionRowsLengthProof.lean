module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
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
open OriginalHereditaryDeletionRowsLengthSyntaxProof OriginalHereditaryDeletionRowsLengthCoreProof
open InternalListCodecSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let front : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let value : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let singleton : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := fields z front value singleton out
  obtain ⟨h⟩ := OriginalHereditaryDeletionRowsLengthCoreProof.zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    front value singleton out ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count))) :
    Nonempty (Derivation body Delta (row (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let front : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let value : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let singleton : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let out : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let A := fields (suc c) front value singleton out
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := OriginalHereditaryDeletionRowsLengthCoreProof.succCore c front value singleton out hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (count : OTerm alpha) : Nonempty (Derivation body Delta (row count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem appendSingletonLength (count front value singleton out : OTerm alpha)
    (hl : Nonempty (Derivation body Delta (lengthGraph count front)))
    (hc : Nonempty (Derivation body Delta (consGraph singleton value z)))
    (ha : Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out front singleton))) :
    Nonempty (Derivation body Delta (lengthGraph (suc count) out)) :=
  rowApply count front value singleton out (allRows count) (andIntro hl (andIntro hc ha))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
