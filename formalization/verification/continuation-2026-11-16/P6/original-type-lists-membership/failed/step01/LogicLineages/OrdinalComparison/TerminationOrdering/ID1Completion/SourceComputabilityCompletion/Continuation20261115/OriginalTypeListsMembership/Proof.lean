module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.CoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.Proof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof hiding OTerm row rowInstantiate rowSuccessor
open InternalBinderTransportProof InternalTermSubstitutionProof InternalPositiveUnfoldingSupportProof
open InternalSourceIntroductionSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro andLeft andRight)
open InductionSyntaxProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
attribute [local irreducible] programGraph

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let allowed : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let types : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let len : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let A := fields z allowed out types len
  have hh : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A) :=
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := BaseProof.zeroCore allowed out types len (andLeft hh) (andRight hh)
  simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (bound : OTerm alpha)
    (hr : Nonempty (Derivation body Delta (row bound))) :
    Nonempty (Derivation body Delta (row (suc bound))) := by
  unfold row
  apply actualFiniteUniversalIntroduction body alpha 4 Delta
  let allowed : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
  let out : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
  let types : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
  let len : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
  let c := bound.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
  let A := fields (suc c) allowed out types len
  let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
  have hr' := InternalGraphCompositionFunctionalityProof.renameInto hr Sum.inl Theta
    (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
  rw [rowRename] at hr'
  have hh : Nonempty (Derivation body Theta A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨h⟩ := CoreProof.successorCore c allowed out types len hr' (andLeft hh) (andRight hh)
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

theorem internalMembership : Targets.InternalMembership := by
  intro body alpha Delta bound allowed out types len hg hl
  obtain ⟨h⟩ := rowApply bound allowed out types len (allRows bound) (andIntro hg hl)
  constructor
  · rintro ⟨hm⟩
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionLeft h) hm⟩
  · rintro ⟨hc⟩
    exact ⟨Derivation.implicationElimination (Derivation.conjunctionRight h) hc⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.Proof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalTypeListsMembership.Proof
