module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open InternalQuotientComparisonSyntaxProof InternalOriginalOrderSyntaxProof
open InternalComputabilityApplicationSyntaxProof (programSubst)
open InternalRawListRecursionSyntaxProof (consTermSubst emptySubst)
open InternalAdditionLawsProof (impSubst)
open OriginalClassContextAllPositionObserver
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

open InternalAcceptanceSupportProof InternalAcceptanceConjunctionProof
open InternalApplicationCertificateConstructorsSupportProof
open InternalLessThanSupportProof (oneConstantValue)
open InternalRawListRecursionSupportProof (recursionNext)
open OriginalTypedDecoderTransportLogicalProof (iffForward iffBackward)
open InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open InternalApplicationStepPeelSupportProof (andLeft andRight)
open OriginalAllPositionRelationScanSyntaxProof

open OriginalAllPositionRelationScanStepProof

theorem zeroRow (R : Program 2) : Nonempty (Derivation body Delta (row R z)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let seed : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let other : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let candidate : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let parameter : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let A := graph4 (scan R) (suc z) z seed other parameter
 let B := graph4 (scan R) (suc z) z seed candidate parameter
 let C := graph4 (scan R) (suc z) z other candidate parameter
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 obtain ⟨hc⟩ := zeroAccepted (body := body) (Delta := B :: Theta) R other candidate parameter
 obtain ⟨hb⟩ := zeroAccepted (body := body) (Delta := C :: Theta) R seed candidate parameter
 have h : Nonempty (Derivation body Theta (B.iff C)) :=
   ⟨Derivation.conjunctionIntroduction (Derivation.implicationIntroduction hc) (Derivation.implicationIntroduction hb)⟩
 obtain ⟨h⟩ := h
 simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem succRow (R : Program 2) (count : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (row R count))) :
 Nonempty (Derivation body Delta (row R (suc count))) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let seed : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let other : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let candidate : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let parameter : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
 let A := graph4 (scan R) (suc z) (suc c) seed other parameter
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have hrow' := renameInto hrow Sum.inl Theta
   (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hrow'
 obtain ⟨h⟩ := succCore R c seed other candidate parameter hrow'
   (show Nonempty (Derivation body Theta A) from ⟨Derivation.hypothesis List.mem_cons_self⟩)
 simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))

theorem allRows (R : Program 2) (count : OTerm alpha) :
 Nonempty (Derivation body Delta (row R count)) := by
 let theta : Formula (alpha ⊕ Fin 1) := row R (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) R)
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
     R (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem scanRow (R : Program 2) (count seed other candidate parameter : OTerm alpha)
 (hit : Nonempty (Derivation body Delta (graph4 (scan R) (suc z) count seed other parameter))) :
 Nonempty (Derivation body Delta ((graph4 (scan R) (suc z) count seed candidate parameter).iff
   (graph4 (scan R) (suc z) count other candidate parameter))) :=
 rowApply R count seed other candidate parameter (allRows R count) hit

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanProof
