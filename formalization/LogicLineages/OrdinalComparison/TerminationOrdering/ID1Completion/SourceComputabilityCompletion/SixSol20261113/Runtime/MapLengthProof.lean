module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthStep
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof (emb z suc zRelabel sucRelabel varBind nextTerm)
open InternalTagArithmeticSupportProof (natInduction)
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open MapLengthSyntax
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroRow (F : Program 1) : Nonempty (Derivation body Delta (row F z)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 2 Delta
 unfold rowBody
 simp only [zRelabel]
 let jobs : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
 let tagged : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
 let A := fields F z jobs tagged
 have hh : Nonempty (Derivation body (A :: Delta.map (fun p => p.relabel Sum.inl)) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
 obtain ⟨h⟩ := SixSol20261113.Context.TermTickMapLengthProof.zero F jobs tagged
   (InternalApplicationStepPeelSupportProof.andLeft hh) (InternalApplicationStepPeelSupportProof.andRight hh)
 exact ⟨Derivation.implicationIntroduction h⟩
theorem successorRow (F : Program 1) (size : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row F size))) :
 Nonempty (Derivation body Delta (row F (suc size))) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 2 Delta
 unfold rowBody
 simp only [sucRelabel]
 let jobs : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
 let tagged : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
 let A := fields F (suc (size.relabel Sum.inl)) jobs tagged
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 2))
 have hi' := renameInto hi Sum.inl Theta
   (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hi'
 obtain ⟨h⟩ := MapLengthStep.successorCore F (size.relabel Sum.inl) jobs tagged hi'
   ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
theorem allRows (F : Program 1) (size : OTerm alpha) : Nonempty (Derivation body Delta (row F size)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row F (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,rowInstantiate,varBind] using (zeroRow F (body := body) (Delta := Delta))
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := successorRow F (body := body) (Delta := theta :: Delta.map weaken)
     (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb size) (natInduction theta hz hs)
 simpa only [theta,rowInstantiate,varBind] using Nonempty.intro h

theorem actualMapLength : MapLengthTargets.ActualMapLength := by
 intro F body alpha Delta size jobs tagged hl ht
 exact rowApply F size jobs tagged (allRows F size) (andIntro hl ht)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Runtime.MapLengthProof
