module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationReflexiveSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationScanStepProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationReflexiveProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalTagArithmeticSupportProof
open InternalGraphCompositionFunctionalityProof
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

open InternalAcceptanceSupportProof
open OriginalAllPositionRelationReflexiveSyntaxProof
open OriginalAllPositionRelationScanStepProof (zeroAccepted successorAccepted)

theorem positionRefl (R : Program 2) (cutoff seed parameter : OTerm alpha) :
 Nonempty (Derivation body Delta (graph4 (positionTest R) (suc z) cutoff seed seed parameter)) := by
 apply programCases (positionObservation R) (Fin.cons cutoff (Fin.cons seed (Fin.cons parameter Fin.elim0))) _
 intro beta j Theta value hj hv
 simp only [graph4Rename,sucRelabel,zRelabel]
 simp only [consTermRename,emptyRename] at hv
 exact OriginalAllPositionRelationPointProof.atCommon R (cutoff.relabel j) (seed.relabel j) (seed.relabel j) (parameter.relabel j) value hv hv

theorem zeroRow (R : Program 2) : Nonempty (Derivation body Delta (OriginalAllPositionRelationReflexiveSyntaxProof.row R z)) := by
 unfold OriginalAllPositionRelationReflexiveSyntaxProof.row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 simpa only [OriginalAllPositionRelationReflexiveSyntaxProof.rowBody,zRelabel] using (zeroAccepted (body := body)
   (Delta := Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))) R
   (.var (.inr 0)) (.var (.inr 0)) (.var (.inr 3)))

theorem succRow (R : Program 2) (count : OTerm alpha)
 (hrow : Nonempty (Derivation body Delta (OriginalAllPositionRelationReflexiveSyntaxProof.row R count))) :
 Nonempty (Derivation body Delta (OriginalAllPositionRelationReflexiveSyntaxProof.row R (suc count))) := by
 unfold OriginalAllPositionRelationReflexiveSyntaxProof.row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let seed : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let parameter : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let c := count.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
 let Theta := Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have hrow' := renameInto hrow Sum.inl Theta (fun p hp => List.mem_map.mpr ⟨p,hp,rfl⟩)
 rw [OriginalAllPositionRelationReflexiveSyntaxProof.rowRename] at hrow'
 have h := successorAccepted R c seed seed parameter
   (OriginalAllPositionRelationReflexiveSyntaxProof.rowApply R c seed parameter hrow') (positionRefl R c seed parameter)
 simpa only [OriginalAllPositionRelationReflexiveSyntaxProof.rowBody,sucRelabel] using h

theorem allRows (R : Program 2) (count : OTerm alpha) :
 Nonempty (Derivation body Delta (OriginalAllPositionRelationReflexiveSyntaxProof.row R count)) := by
 let theta : Formula (alpha ⊕ Fin 1) := OriginalAllPositionRelationReflexiveSyntaxProof.row R (.var (.inr 0))
 have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
   simpa only [theta,OriginalAllPositionRelationReflexiveSyntaxProof.rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta) R)
 have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
   have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
     R (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
   simpa only [theta,OriginalAllPositionRelationReflexiveSyntaxProof.rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
 obtain ⟨hz⟩ := hz
 obtain ⟨hs⟩ := hs
 have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
 simpa only [theta,OriginalAllPositionRelationReflexiveSyntaxProof.rowInstantiate,varBind] using (Nonempty.intro h)

theorem scanRefl (R : Program 2) (count seed parameter : OTerm alpha) :
 Nonempty (Derivation body Delta (graph4 (scan R) (suc z) count seed seed parameter)) :=
 OriginalAllPositionRelationReflexiveSyntaxProof.rowApply R count seed parameter (allRows R count)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationReflexiveProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalAllPositionRelationReflexiveProof
