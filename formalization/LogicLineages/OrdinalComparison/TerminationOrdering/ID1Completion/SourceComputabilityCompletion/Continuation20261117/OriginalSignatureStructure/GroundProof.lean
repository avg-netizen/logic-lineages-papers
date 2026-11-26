module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.GroundCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.GroundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof hiding OTerm row rowInstantiate rowSuccessor
open InternalBinderTransportProof InternalTermSubstitutionProof InternalPositiveUnfoldingSupportProof
open InternalSourceIntroductionSyntaxProof
open GroundSyntaxProof GroundCoreProof
open Continuation20261116.OriginalConcreteHeadSignature
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 2 Delta
  let out : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let index : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let A := graph1 groundList out z
  obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
    out index ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (bound : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row bound))) :
    Nonempty (Derivation body Delta (row (suc bound))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 2 Delta
  let out : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let index : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  let c := bound.relabel (Sum.inl : alpha → alpha ⊕ Fin 2)
  let A := graph1 groundList out (suc c)
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hr'
  obtain ⟨h⟩ := succCore c out index hr' ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (bound : OTerm alpha) : Nonempty (Derivation body Delta (row bound)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb bound) (InternalTagArithmeticSupportProof.natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem groundListStructure : Targets.InternalGroundListStructure := by
  intro body alpha Delta count args hg
  have hr := allRows (body := body) (Delta := Delta) count
  constructor
  · exact InternalApplicationStepPeelSupportProof.andLeft (rowApply count args z hr hg)
  · intro index
    exact InternalApplicationStepPeelSupportProof.andRight (rowApply count args index hr hg)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.GroundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261117.OriginalSignatureStructure.GroundProof
