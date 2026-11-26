module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel varBind nextTerm)
open InternalTagArithmeticSupportProof (natInduction)
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ContentVisitsDefinitions ContentVisitsSyntax ContentVisitsInductionSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroRow (R : Program 2) : Nonempty (Derivation body Delta (row R z)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 unfold rowBody
 simp only [zRelabel]
 let jobs : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let tagged : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let forward : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let produced : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let A := fields R z jobs tagged forward produced
 obtain ⟨h⟩ := ContentVisitsBaseProof.zeroCore R (body := body)
   (Delta := A :: Delta.map (fun p => p.relabel Sum.inl)) jobs tagged forward produced ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
theorem successorRow (R : Program 2) (size : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row R size))) :
 Nonempty (Derivation body Delta (row R (suc size))) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 unfold rowBody
 simp only [sucRelabel]
 let jobs : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let tagged : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let forward : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let produced : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let A := fields R (suc (size.relabel Sum.inl)) jobs tagged forward produced
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have hi' := renameInto hi Sum.inl Theta
   (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hi'
 obtain ⟨h⟩ := ContentVisitsStepProof.successorCore R (size.relabel Sum.inl) jobs tagged forward produced hi'
   ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
theorem allRows (R : Program 2) (size : OTerm alpha) : Nonempty (Derivation body Delta (row R size)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row R (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,rowInstantiate,varBind] using (zeroRow R (body := body) (Delta := Delta))
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := successorRow R (body := body) (Delta := theta :: Delta.map weaken)
     (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb size) (natInduction theta hz hs)
 simpa only [theta,rowInstantiate,varBind] using Nonempty.intro h

theorem actualMappedVisits : ContentVisitsTargets.ActualMappedVisits := by
 intro R body alpha Delta size jobs tagged forward produced hl ht ha hv hm hr
 exact rowApply R size jobs tagged forward produced (allRows R size)
   (andIntro hl (andIntro ht (andIntro ha (andIntro hv (andIntro hm hr)))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Erasure.ContentVisitsProof
