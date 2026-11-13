module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationCore
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof (renameInto)
open InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof (natInduction)
open InternalBinderTransportProof InternalTermSubstitutionProof InternalSourceIntroductionSyntaxProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalApplicationStepPeelSupportProof (andIntro)
open AppendReassociationSyntax AppendReassociationCore
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}
theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 let a : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let b : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let c : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let ab : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let bc : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let out : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let A := fields z a b c ab bc out
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
 obtain ⟨h⟩ := zeroCore (body:=body) (Delta:=Theta) a b c ab bc out ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))
theorem succRow (count : OTerm alpha) (hi : Nonempty (Derivation body Delta (row count))) :
 Nonempty (Derivation body Delta (row (suc count))) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 let a : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let b : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let c : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let ab : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let bc : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let out : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let dep := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 6)
 let A := fields (suc dep) a b c ab bc out
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
 have hi' := renameInto hi Sum.inl Theta (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hi'
 obtain ⟨h⟩ := succCore dep (body:=body) (Delta:=Theta) a b c ab bc out hi' ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,zRelabel,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))
theorem allRows (count : OTerm alpha) : Nonempty (Derivation body Delta (row count)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,rowInstantiate,varBind] using (zeroRow (body:=body) (Delta:=Delta))
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := succRow (body:=body) (Delta:=theta :: Delta.map weaken)
     (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)
theorem appendReassociation : ProtectedAgendaWorkingTargets.AppendReassociation := by
 intro body alpha Delta a b c ab bc out hab hbc hout
 apply programCases OriginalContextInsertion.length (Fin.cons a Fin.elim0) _
 intro beta j Theta count hinc hl
 simp only [consTermRename,emptyRename] at hl
 have hab' := renameInto hab j Theta hinc
 have hbc' := renameInto hbc j Theta hinc
 have hout' := renameInto hout j Theta hinc
 simp only [graph2Rename] at hab' hbc' hout'
 rw [graph2Rename]
 exact rowApply count (a.relabel j) (b.relabel j) (c.relabel j) (ab.relabel j) (bc.relabel j) (out.relabel j)
   (allRows count) (andIntro hl (andIntro hab' (andIntro hbc' hout')))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Runtime.AppendReassociationProof
