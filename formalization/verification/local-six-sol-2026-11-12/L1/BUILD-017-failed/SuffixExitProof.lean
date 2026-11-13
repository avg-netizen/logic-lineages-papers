module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitCore
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof (natInduction)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalRecursionGraphSyntaxProof InternalRecursionClosureSyntaxProof
open InternalApplicationStepPeelSupportProof (andIntro)
open SuffixExitWorkingTargets SuffixExitSyntax SuffixExitCore
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroRow (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output : OTerm alpha) (psi : Formula alpha)
 (next : Consumer R body Delta suffix output psi) :
 Nonempty (Derivation body Delta (row R H M W c B suffix output z psi)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let input : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let work : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let results : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let front : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let A := fields R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (suffix.relabel Sum.inl)
   (output.relabel Sum.inl) z input work results front
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 4) ∈ Theta :=
   fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 obtain ⟨h⟩ := zeroCore (body:=body) (Delta:=Theta) R H M W
   (c.relabel Sum.inl) (B.relabel Sum.inl) (suffix.relabel Sum.inl) (output.relabel Sum.inl)
   input work results front (psi.relabel Sum.inl) ⟨Derivation.hypothesis List.mem_cons_self⟩
   (renameConsumer R suffix output psi Sum.inl Theta next inc)
 simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))
theorem succRow (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count : OTerm alpha) (psi : Formula alpha)
 (hi : Nonempty (Derivation body Delta (row R H M W c B suffix output count psi)))
 (next : Consumer R body Delta suffix output psi) :
 Nonempty (Derivation body Delta (row R H M W c B suffix output (suc count) psi)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let input : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let work : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let results : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let front : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let A := fields R H M W (c.relabel Sum.inl) (B.relabel Sum.inl) (suffix.relabel Sum.inl)
   (output.relabel Sum.inl) (suc (count.relabel Sum.inl)) input work results front
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 4) ∈ Theta :=
   fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
 have hi' := renameInto hi Sum.inl Theta inc
 rw [rowRename] at hi'
 obtain ⟨h⟩ := succCore (body:=body) (Delta:=Theta) R H M W
   (c.relabel Sum.inl) (B.relabel Sum.inl) (suffix.relabel Sum.inl) (output.relabel Sum.inl) (count.relabel Sum.inl)
   input work results front (psi.relabel Sum.inl) hi' ⟨Derivation.hypothesis List.mem_cons_self⟩
   (renameConsumer R suffix output psi Sum.inl Theta next inc)
 simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))
theorem allRows (R : Program 2) (H : Program 1) (M W : Program 2)
 (c B suffix output count : OTerm alpha) (psi : Formula alpha)
 (next : Consumer R body Delta suffix output psi) :
 Nonempty (Derivation body Delta (row R H M W c B suffix output count psi)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row R H M W (c.relabel Sum.inl) (B.relabel Sum.inl)
   (suffix.relabel Sum.inl) (output.relabel Sum.inl) (.var (.inr 0)) (psi.relabel Sum.inl)
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,rowInstantiate,liftBind,varBind,formulaBind] using
     (zeroRow (body:=body) (Delta:=Delta) R H M W c B suffix output psi next)
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have inc : ∀ f ∈ Delta, f.relabel (Sum.inl : alpha → alpha ⊕ Fin 1) ∈ theta :: Delta.map weaken :=
     fun f hf => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨f,hf,rfl⟩)
   have h := succRow (body:=body) (Delta:=theta :: Delta.map weaken) R H M W
     (c.relabel Sum.inl) (B.relabel Sum.inl) (suffix.relabel Sum.inl) (output.relabel Sum.inl)
     (.var (.inr (0 : Fin 1))) (psi.relabel Sum.inl) ⟨Derivation.hypothesis List.mem_cons_self⟩
     (renameConsumer R suffix output psi Sum.inl (theta :: Delta.map weaken) next inc)
   simpa only [theta,rowSuccessor,nextLift,nextTerm,Term.subst,Sum.elim_inr,formulaNext] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,rowInstantiate,liftBind,varBind,formulaBind] using (Nonempty.intro h)
theorem actualExit : SuffixExitWorkingTargets.ActualExit := by
 intro R H M W body alpha Delta c B suffix output count input work results front psi hs ha happ hr he next
 exact rowApply R H M W c B suffix output count input work results front psi
   (allRows R H M W c B suffix output count psi next)
   (andIntro hs (andIntro ha (andIntro happ (andIntro hr he))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.SuffixExitProof
