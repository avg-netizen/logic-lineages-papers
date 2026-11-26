module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionProof
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
open OriginalResultStackPartitionSyntaxProof OriginalResultStackPartitionCoreProof
open InternalListCodecSupportProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  let initialList : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let suffix : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let joined : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let A := fields z initialList suffix joined
  obtain ⟨h⟩ := OriginalResultStackPartitionCoreProof.zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    initialList suffix joined ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (count : OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count))) :
    Nonempty (Derivation body Delta (row (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 3 Delta
  let initialList : OTerm (alpha ⊕ Fin 3) := .var (.inr 0)
  let suffix : OTerm (alpha ⊕ Fin 3) := .var (.inr 1)
  let joined : OTerm (alpha ⊕ Fin 3) := .var (.inr 2)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 3)
  let A := fields (suc c) initialList suffix joined
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 3))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  obtain ⟨h⟩ := OriginalResultStackPartitionCoreProof.succCore c initialList suffix joined hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
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

theorem actualPartition : OriginalResultStackPartitionTargets.ActualPartition := by
 intro body alpha Delta count initialList suffix joined hl ha
 exact rowApply count initialList suffix joined (allRows count) (andIntro hl ha)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalResultStackPartitionProof
