module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalFiniteBlocksSubstitutionProof InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalOriginalOrderSyntaxProof InternalOriginalPairingOrderArithmeticProof
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalClassContextAllPositionObserver OriginalAllPositionContextDeleteFrontCoreProof
open OriginalAllPositionContextDeleteFrontSyntaxProof OriginalAllPositionContextDeleteFrontBaseProof
open OriginalAllPositionContextDeleteFrontCoreProof
open InternalListCodecSupportProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem succRow (count : InternalGraphComposition.OTerm alpha)
    (hrow : Nonempty (Derivation body Delta (row count))) :
    Nonempty (Derivation body Delta (row (suc count))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 5 Delta
  let gamma : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
  let head : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
  let tail : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
  let previous : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
  let out : InternalGraphComposition.OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
  let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 5)
  let A := consGraph gamma head tail ⊓ (graph2 front previous (suc c) tail ⊓ consGraph out head previous)
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
  have hrow' := renameInto hrow Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hrow'
  have ha : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := succCore c gamma head tail previous out hrow'
    (andLeft ha) (andLeft (andRight ha)) (andRight (andRight ha))
  simpa only [rowBody,sucRelabel] using Nonempty.intro (Derivation.implicationIntroduction h)

theorem allRows (count : InternalGraphComposition.OTerm alpha) :
    Nonempty (Derivation body Delta (row count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) (alpha := alpha))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using Nonempty.intro h

theorem frontCons (gamma head tail cutoff previous out : InternalGraphComposition.OTerm alpha)
    (hc : Nonempty (Derivation body Delta (consGraph gamma head tail)))
    (hp : Nonempty (Derivation body Delta (graph2 front previous cutoff tail)))
    (ho : Nonempty (Derivation body Delta (consGraph out head previous))) :
    Nonempty (Derivation body Delta (graph2 front out (suc cutoff) gamma)) :=
  rowApply cutoff gamma head tail previous out (allRows cutoff) hc hp ho

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionContextDeleteFrontProof
