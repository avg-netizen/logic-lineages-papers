module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupQueryProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalHereditaryDeletionRows OriginalInternalAppendLookupSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open OriginalInternalAppendLookupCoreProof OriginalInternalAppendLookupQueryProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 let front : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let suffix : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let joined : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let count : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let index : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let value : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let A := fields z front suffix joined count index value
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
 obtain ⟨h⟩ := zeroCore (body := body) (Delta := Theta) front suffix joined count index value ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,zRelabel,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))
theorem succRow (frontCount : OTerm alpha) (hi : Nonempty (Derivation body Delta (row frontCount))) :
 Nonempty (Derivation body Delta (row (suc frontCount))) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 let front : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let suffix : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let joined : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let count : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let index : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let value : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let dep := frontCount.relabel (Sum.inl : alpha → alpha ⊕ Fin 6)
 let A := fields (suc dep) front suffix joined count index value
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
 have hi' := renameInto hi Sum.inl Theta (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hi'
 obtain ⟨h⟩ := succCore dep (body := body) (Delta := Theta) front suffix joined count index value hi' ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,zRelabel,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))
theorem allRows (frontCount : OTerm alpha) : Nonempty (Derivation body Delta (row frontCount)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb frontCount) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem actualSplit : OriginalInternalAppendLookupTargets.ActualSplit := by
 intro body alpha Delta frontCount front suffix joined count index value hl ha hj hb hv
 exact rowApply frontCount front suffix joined count index value (allRows frontCount)
   (InternalApplicationStepPeelSupportProof.andIntro hl (InternalApplicationStepPeelSupportProof.andIntro ha
     (InternalApplicationStepPeelSupportProof.andIntro hj (InternalApplicationStepPeelSupportProof.andIntro hb hv))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalInternalAppendLookupProof
