module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceCoreProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalApplicationStepPeelSupportProof (andLeft andRight andIntro)
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open OriginalHereditaryDeletionRowsCongruenceSyntaxProof OriginalHereditaryDeletionRowsCongruenceCoreProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow (Q : Program 2) : Nonempty (Derivation body Delta (row Q z)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 let input : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let parameter : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let other : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let otherParameter : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let left : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let right : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let A := fields Q z input parameter other otherParameter left right
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
 obtain ⟨h⟩ := zeroCore Q input parameter other otherParameter left right (body := body) (Delta := Theta) ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (Q : Program 2) (count : OTerm alpha)
 (hi : Nonempty (Derivation body Delta (row Q count))) : Nonempty (Derivation body Delta (row Q (suc count))) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 6 Delta
 let input : OTerm (alpha ⊕ Fin 6) := .var (.inr 0)
 let parameter : OTerm (alpha ⊕ Fin 6) := .var (.inr 1)
 let other : OTerm (alpha ⊕ Fin 6) := .var (.inr 2)
 let otherParameter : OTerm (alpha ⊕ Fin 6) := .var (.inr 3)
 let left : OTerm (alpha ⊕ Fin 6) := .var (.inr 4)
 let right : OTerm (alpha ⊕ Fin 6) := .var (.inr 5)
 let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 6)
 let A := fields Q (suc c) input parameter other otherParameter left right
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 6))
 have hi' := renameInto hi Sum.inl Theta (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hi'
 obtain ⟨h⟩ := succCore Q c input parameter other otherParameter left right (body := body) (Delta := Theta) hi' ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (Q : Program 2) (count : OTerm alpha) : Nonempty (Derivation body Delta (row Q count)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row Q (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,rowInstantiate,varBind] using (zeroRow Q (body := body) (Delta := Delta))
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := succRow Q (body := body) (Delta := theta :: Delta.map weaken)
     (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem exactCongruence : OriginalHereditaryDeletionRowsCongruenceTargets.ScanCongruence := by
 intro Q body alpha Delta count input parameter other otherParameter left right
 let A := fields Q count input parameter other otherParameter left right
 obtain ⟨h⟩ := rowApply Q count input parameter other otherParameter left right
   (allRows Q count (body := body) (Delta := A :: Delta)) ⟨Derivation.hypothesis List.mem_cons_self⟩
 exact ⟨Derivation.implicationIntroduction h⟩
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCongruenceProof
