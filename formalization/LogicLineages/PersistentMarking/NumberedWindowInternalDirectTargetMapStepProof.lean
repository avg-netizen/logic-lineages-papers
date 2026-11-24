module
public import LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapStepTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalDirectSharedTapeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalAtomicRefinementObjectEmitterProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceNormalizationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapStep
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
open ID1Completion.InternalAcceptance (conjunction constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim zeroBranchIntro)
open ID1Completion.InternalAcceptanceNormalizationProof (normalizeReject)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept constantZeroValue)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover programCompositionCases)
open ID1Completion.InternalControlGraphSupportProof
  (projectionValue outputTransport zeroSuccessorCases valueUnique successorValue programRename)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (formulaRelabelComposition)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn sucRelabel zRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply cancelSuc)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram GorbowVerifierNormalization
open NumberedWindowInternalDirectTargetMapStepTargets
open NumberedWindowInternalDirectInsertedTargetsMapTargets (targetStep joined atHead)
open NumberedWindowInternalDirectSharedTapeSyntaxProof (renamePair)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (binaryInputsRename)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (inputsRename)
open NumberedWindowInternalDirectWitnessEnvelopeTargets (guardAt)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary suc z)
open NumberedWindowInternalFreshProbeDispatchProgram (literal)
open NumberedWindowInternalAtomicRefinementObjectEmitterProof (literalGraph)

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private def guard : Program 2 := atHead (guardAt 4)
private def guardControl : Program 2 := conjunction guard (literal 2 1)
private def succJoined : Program 2 := .composition .succ (Fin.cons joined Fin.elim0)
private def inner : Program 2 := ID1Completion.InternalAcceptance.branch (.projection 1) (constantZero 2) succJoined

private theorem zeroImpossible (x y out : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph (constantZero 2) (suc out) ![x,y]))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  obtain ⟨q⟩ := valueUnique (constantZero 2) (suc out) z ![x,y] h (constantZeroValue ![x,y])
  exact ⟨sucNeZeroApply q⟩

private theorem actualGuard (row prev : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph guard (suc z) ![row,prev]))) :
    Nonempty (Derivation B Γ (unary (guardAt 4) (suc z) row)) := by
  apply compositionRecover (guardAt 4) (Fin.cons (.projection 0) Fin.elim0)
    (suc z) ![row,prev] ![row] h
  intro i
  obtain rfl := Fin.eq_zero i
  exact projectionValue 0 ![row,prev]

private theorem removeSuccessor (row prev out : OTerm α)
    (h : Nonempty (Derivation B Γ (programGraph succJoined (suc out) ![row,prev]))) :
    Nonempty (Derivation B Γ (programGraph joined out ![row,prev])) := by
  apply programCompositionCases .succ (Fin.cons joined Fin.elim0) (suc out) ![row,prev] _ h
  intro β j values Δ _ ran observed
  simp only [programRename,binaryInputsRename]
  simp only [sucRelabel] at ran
  obtain ⟨e⟩ := valueUnique .succ (suc (out.relabel j)) (suc (values 0)) values ran
    (successorValue values)
  have hit := observed (0 : Fin 1)
  change Nonempty (Derivation B Δ
    (programGraph joined (values 0) (fun i : Fin 2 => ((![row,prev] : Fin 2 → OTerm α) i).relabel j))) at hit
  rw [binaryInputsRename] at hit
  exact outputTransport joined (values 0) (out.relabel j) ![row.relabel j,prev.relabel j]
    ⟨cancelSuc (ID1Completion.InternalTagArithmeticSupportProof.symm e)⟩ hit

private theorem rejectGuard (row prev out : OTerm α)
    (no : Nonempty (Derivation B Γ (programGraph guard (suc z) ![row,prev]).not))
    (h : Nonempty (Derivation B Γ (programGraph targetStep (suc out) ![row,prev]))) :
    Nonempty (Derivation B Γ (⊥ : Formula α)) := by
  let xs : Fin 2 → OTerm α := ![row,prev]
  have failed := normalizeReject guard xs no
  have q : Nonempty (Derivation B Γ (programGraph guardControl z xs)) :=
    zeroBranchIntro (normalize guard) (constantZero 2) (normalize (literal 2 1)) z xs
      failed (constantZeroValue xs)
  exact zeroImpossible row prev out
    (zeroBranchElim guardControl (constantZero 2) inner (suc out) xs q h)

theorem exactOpenTargetMapStep : ExactOpenTargetMapStep := by
  intro B α Γ row previous projected goal hit next
  let G := programGraph guard (suc z) ![row,previous]
  apply formulaCases G goal
  · have good : Nonempty (Derivation B (G :: Γ) G) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨h⟩ := hit
    have G1 := conjunctionAccept guard (literal 2 1) ![row,previous] good (literalGraph 1 ![row,previous])
    have now := successorBranchElim guardControl (constantZero 2) inner (suc projected) z
      ![row,previous] G1 ⟨addHyp h G⟩
    apply zeroSuccessorCases (G :: Γ) previous goal
    · let E := eqn previous z
      obtain ⟨held⟩ := now
      have hz : Nonempty (Derivation B (E :: G :: Γ) E) :=
        ⟨Derivation.hypothesis List.mem_cons_self⟩
      have p := outputTransport (.projection 1) previous z ![row,previous] hz
        (projectionValue 1 ![row,previous])
      obtain ⟨bad⟩ := zeroImpossible row previous projected
        (zeroBranchElim (.projection 1) (constantZero 2) succJoined (suc projected)
          ![row,previous] p ⟨addHyp held E⟩)
      exact ⟨Derivation.explosion bad⟩
    · intro β j Δ tail keep e
      let h := row.relabel j
      let p := previous.relabel j
      let q := projected.relabel j
      have report : Nonempty (Derivation B Δ (programGraph inner (suc q) ![h,p])) := by
        simpa only [h,p,q,sucRelabel] using renamePair inner (suc projected) row previous now j keep
      have g : Nonempty (Derivation B Δ (programGraph guard (suc z) ![h,p])) := by
        simpa only [h,p,sucRelabel,zRelabel] using renamePair guard (suc z) row previous good j keep
      have prev := outputTransport (.projection 1) p (suc tail) ![h,p] e (projectionValue 1 ![h,p])
      have branch := successorBranchElim (.projection 1) (constantZero 2) succJoined
        (suc q) tail ![h,p] prev report
      exact next β j Δ tail (fun f hf => keep f (List.mem_cons_of_mem _ hf)) e
        (actualGuard h p g) (removeSuccessor h p q branch)
  · obtain ⟨held⟩ := hit
    have no : Nonempty (Derivation B (G.not :: Γ) G.not) :=
      ⟨Derivation.hypothesis List.mem_cons_self⟩
    obtain ⟨bad⟩ := rejectGuard row previous projected no ⟨addHyp held G.not⟩
    exact ⟨Derivation.explosion bad⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalDirectTargetMapStep
