module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsLengthProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundSyntaxProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryDeletionRowsCasesProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundCoreProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundQueryProof
public meta import LogicLineages.Audit
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationStepPeelSupportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationStepPeel (graph5)
open InternalApplicationStepPeelSupportProof (graph5Rename)
open InternalApplicationCertificateConstructors InternalApplicationCertificateConstructorsSyntaxProof
open SourceComputabilityFormulaSupportProof InternalClosedPrograms InternalClosedProgramsBindingProof
open InternalControlGraphSupportProof InternalAcceptanceSupportProof
open InternalGraphCompositionFunctionalityProof InternalRecursionGraphStepSyntaxProof
open InternalTagArithmeticSyntaxProof hiding row rowInstantiate rowSuccessor
open InternalTagArithmeticSupportProof InternalBinderTransportProof InternalTermSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalFiniteBlocksSubstitutionProof
open InternalRecursionClosureSyntaxProof InternalRecursionGraphSyntaxProof
open OriginalContextInsertion OriginalContextInsertionSyntaxProof OriginalContextInsertionLengthProof
open OriginalHereditaryDeletionRows OriginalHereditaryBudgetSumBoundSyntaxProof
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open InternalListCodecSupportProof
open OriginalHereditaryBudgetSumBoundCoreProof OriginalHereditaryBudgetSumBoundQueryProof
variable {body : Positive (Fin 1)} {alpha : Type} {Delta : List (Formula alpha)}

theorem zeroRow : Nonempty (Derivation body Delta (row z)) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let b : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let c : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let v : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let w : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let A := fields z b c v w
 obtain ⟨h⟩ := zeroCore (body := body) (Delta := A :: Delta.map (fun p => p.relabel Sum.inl))
   b c v w ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,zRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))
theorem succRow (depth : OTerm alpha) (hi : Nonempty (Derivation body Delta (row depth))) :
 Nonempty (Derivation body Delta (row (suc depth))) := by
 unfold row
 apply actualFiniteUniversalIntroduction body alpha 4 Delta
 let b : OTerm (alpha ⊕ Fin 4) := .var (.inr 0)
 let c : OTerm (alpha ⊕ Fin 4) := .var (.inr 1)
 let v : OTerm (alpha ⊕ Fin 4) := .var (.inr 2)
 let w : OTerm (alpha ⊕ Fin 4) := .var (.inr 3)
 let dep := depth.relabel (Sum.inl : alpha → alpha ⊕ Fin 4)
 let A := fields (suc dep) b c v w
 let Theta := A :: Delta.map (fun p => p.relabel (Sum.inl : alpha → alpha ⊕ Fin 4))
 have hi' := renameInto hi Sum.inl Theta (fun p hp => List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩))
 rw [rowRename] at hi'
 obtain ⟨h⟩ := succCore dep b c v w hi' ⟨Derivation.hypothesis List.mem_cons_self⟩
 simpa only [rowBody,sucRelabel] using (Nonempty.intro (Derivation.implicationIntroduction h))
theorem allRows (count : OTerm alpha) : Nonempty (Derivation body Delta (row count)) := by
  let theta : Formula (alpha ⊕ Fin 1) := row (.var (.inr 0))
  have hz : Nonempty (Derivation body Delta (instantiate theta (emb z))) := by
    simpa only [theta,rowInstantiate,varBind] using (zeroRow (body := body) (Delta := Delta))
  have hs : Nonempty (Derivation body (theta :: Delta.map weaken) (successorInstance theta)) := by
    have h := succRow (body := body) (Delta := theta :: Delta.map weaken)
      (.var (.inr (0 : Fin 1))) ⟨Derivation.hypothesis List.mem_cons_self⟩
    simpa only [theta,rowSuccessor,nextTerm,Term.subst,Sum.elim_inr] using h
  obtain ⟨hz⟩ := hz
  obtain ⟨hs⟩ := hs
  have h := Derivation.universalElimination (emb count) (natInduction theta hz hs)
  simpa only [theta,rowInstantiate,varBind] using (Nonempty.intro h)

theorem actualMajorization : OriginalHereditaryBudgetSumBoundTargets.Majorization := by
 intro body alpha Delta depth b c v w hb hv hw
 exact rowApply depth b c v w (allRows depth)
   (InternalApplicationStepPeelSupportProof.andIntro hb (InternalApplicationStepPeelSupportProof.andIntro hv hw))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundProof
#audit_namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalHereditaryBudgetSumBoundProof
