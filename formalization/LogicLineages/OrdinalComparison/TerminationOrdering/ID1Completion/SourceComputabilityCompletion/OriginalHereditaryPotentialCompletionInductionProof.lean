module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionInductionProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalTagArithmeticSyntaxProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalSourceIntroductionSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalRecursionGraphSyntaxProof InternalRecursionClosureSyntaxProof
open InternalPositiveUnfoldingSupportProof
open OriginalHereditaryPotentialCompletion OriginalHereditaryPotentialCompletionSyntaxProof
open OriginalHereditaryPotentialCompletionCoreProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroRow (R : Program 2) (H : Program 1) (M W : Program 2) (supply : StepLaw R H M W)
 (c B : OTerm alpha) : Nonempty (Derivation body Delta (Row R H M W c B z)) := by
 unfold Row
 apply actualFiniteUniversalIntroduction body alpha 5 Delta
 let input : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let work : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let results : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let before : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let output : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let A := Entry R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) z input work results before output
 obtain ⟨d⟩ := zeroCore (body:=body) (Delta:=A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))) R H M W supply
  (c.relabel Sum.inl) (B.relabel Sum.inl) input work results before output ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))
theorem succRow (R : Program 2) (H : Program 1) (M W : Program 2) (supply : StepLaw R H M W)
 (c B fuel : OTerm alpha) (hrow : Nonempty (Derivation body Delta (Row R H M W c B fuel))) :
 Nonempty (Derivation body Delta (Row R H M W c B (suc fuel))) := by
 unfold Row
 apply actualFiniteUniversalIntroduction body alpha 5 Delta
 let input : OTerm (alpha ⊕ Fin 5) := .var (.inr 0)
 let work : OTerm (alpha ⊕ Fin 5) := .var (.inr 1)
 let results : OTerm (alpha ⊕ Fin 5) := .var (.inr 2)
 let before : OTerm (alpha ⊕ Fin 5) := .var (.inr 3)
 let output : OTerm (alpha ⊕ Fin 5) := .var (.inr 4)
 let A := Entry R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (suc (fuel.relabel Sum.inl)) input work results before output
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 5))
 have hrow' := renameInto hrow Sum.inl Theta (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hrow'
 obtain ⟨d⟩ := successorCore (body:=body) (Delta:=Theta) R H M W supply (c.relabel Sum.inl) (B.relabel Sum.inl) (fuel.relabel Sum.inl)
  input work results before output hrow' ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction d))
theorem allRows (R : Program 2) (H : Program 1) (M W : Program 2) (supply : StepLaw R H M W)
 (c B fuel : OTerm alpha) : Nonempty (Derivation body Delta (Row R H M W c B fuel)) := by
 let theta : Formula (alpha ⊕ Fin 1) := Row R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
  simpa only [theta,rowInstantiate,liftBind,varBind] using (zeroRow (body:=body) (Delta:=Delta) R H M W supply c B)
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
  have h := succRow (body:=body) (Delta:=theta :: Delta.map weaken) R H M W supply
    (c.relabel Sum.inl) (B.relabel Sum.inl) (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
  simpa only [theta,rowSuccessor,nextLift,nextTerm,Term.subst,Sum.elim_inr] using h
 have h := Derivation.universalElimination (emb fuel) (natInduction theta (Classical.choice hz) (Classical.choice hs))
 simpa only [theta,rowInstantiate,liftBind,varBind] using (Nonempty.intro h)
theorem conditionalCompletion : OriginalHereditaryPotentialCompletionTargets.ConditionalCompletion := by
 intro R H M W supply body alpha Delta c B fuel input work results before output he
 exact rowApply R H M W c B fuel input work results before output (allRows R H M W supply c B fuel) he
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionInductionProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryPotentialCompletionInductionProof
