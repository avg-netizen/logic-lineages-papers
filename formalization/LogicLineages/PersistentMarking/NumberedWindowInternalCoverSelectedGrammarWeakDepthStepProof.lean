module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthEqualityProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBindingProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthBaseProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarDepthInductionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthObservationProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverObjectInclusionTransitivityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalSourceInversionSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendTransitionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthStepProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc zRelabel sucRelabel)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalLeastNumberProof (actualRightSuccessorSplit)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalBetaTotalityProof (disjunctionElimination)
open ID1Completion.InternalApplicationValidityStackAppendTransitionProof (notLessZero)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (withHyp)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalCoverSelectedGrammarWidthTargets (observed pairInclusion)
open NumberedWindowInternalCoverSelectedGrammarWidthObservationProof (observationCases)
open NumberedWindowInternalCoverSelectedGrammarWidthSyntaxProof (observedRename)
open NumberedWindowInternalCoverSelectedGrammarDepthTargets (depthAt)
open NumberedWindowInternalCoverSelectedGrammarDepthBindingProof (buildDepth consumeDepth)
open NumberedWindowInternalCoverSelectedGrammarDepthSyntaxProof (depthRename)
open NumberedWindowInternalCoverSelectedGrammarDepthBaseProof (inclusionRename)
open NumberedWindowInternalCoverSelectedGrammarDepthInductionProof (exact_OpenSelectedGrammarAdjacentDepth)
open NumberedWindowInternalCoverObjectInclusionTransitivityProof (composePair)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthTargets
open NumberedWindowInternalCoverSelectedGrammarWeakDepthBindingProof (buildLower useLower)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthSyntaxProof (lowerRename)
open NumberedWindowInternalCoverSelectedGrammarWeakDepthEqualityProof (equalDepth)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem splitWeak (d D : OTerm α)
    (weak : Nonempty (Derivation body Γ (ltF d (suc D)))) :
    Nonempty (Derivation body Γ (ltF d D ⊔ eqn d D)) := by
  obtain ⟨h⟩ := actualRightSuccessorSplit body α d D
  rw [onEquality] at h
  obtain ⟨weak⟩ := weak
  exact ⟨Derivation.implicationElimination (weakenClosed h Γ) weak⟩

private theorem atZero (d H K M : OTerm α)
    (weak : Nonempty (Derivation body Γ (ltF d (suc z)))) :
    Nonempty (Derivation body Γ (depthAt d z H K M)) := by
  obtain ⟨which⟩ := splitWeak d z weak
  let L := ltF d z
  let R := eqn d z
  obtain ⟨never⟩ := notLessZero (body := body) (Gamma := L :: Γ) d
  have contradiction := Derivation.implicationElimination never
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨same⟩ := equalDepth (body := body) (Γ := R :: Γ) d z H K M
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination which (Derivation.implicationIntroduction (Derivation.explosion contradiction))
    (Derivation.implicationIntroduction same)⟩

theorem lowerAtZero (H K M : OTerm α) :
    Nonempty (Derivation body Γ (allLower z H K M)) := by
  apply buildLower z H K M
  intro β j Δ d keep actual
  simp only [zRelabel] at actual ⊢
  exact atZero d (H.relabel j) (K.relabel j) (M.relabel j) actual

private theorem throughMiddle (d D H K M old oldTerms oldArgs next nextTerms nextArgs : OTerm α)
    (ih : Nonempty (Derivation body Γ (depthAt d D H K M)))
    (small : Nonempty (Derivation body Γ (observed d H K M old oldTerms oldArgs)))
    (large : Nonempty (Derivation body Γ (observed (suc D) H K M next nextTerms nextArgs))) :
    Nonempty (Derivation body Γ (pairInclusion oldTerms nextTerms oldArgs nextArgs)) := by
  apply observationCases D H K M _
  intro β j Δ mid midTerms midArgs keep actual
  rw [inclusionRename]
  have previous := renameInto ih j Δ keep
  have first := renameInto small j Δ keep
  have last := renameInto large j Δ keep
  rw [depthRename] at previous
  rw [observedRename] at first
  rw [observedRename,sucRelabel] at last
  have fromLow := consumeDepth (d.relabel j) (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    (old.relabel j) (oldTerms.relabel j) (oldArgs.relabel j) mid midTerms midArgs previous first actual
  have toHigh := exact_OpenSelectedGrammarAdjacentDepth body β Δ
    (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) mid midTerms midArgs
    (next.relabel j) (nextTerms.relabel j) (nextArgs.relabel j) actual last
  exact composePair body β Δ (oldTerms.relabel j) midTerms (nextTerms.relabel j)
    (oldArgs.relabel j) midArgs (nextArgs.relabel j) fromLow toHigh

private theorem earlierAtNext (d D H K M : OTerm α)
    (ih : Nonempty (Derivation body Γ (allLower D H K M)))
    (early : Nonempty (Derivation body Γ (ltF d (suc D)))) :
    Nonempty (Derivation body Γ (depthAt d (suc D) H K M)) := by
  have previous := useLower d D H K M ih early
  apply buildDepth d (suc D) H K M
  intro β j Δ old oldTerms oldArgs next nextTerms nextArgs keep small large
  have prev := renameInto previous j Δ keep
  rw [depthRename] at prev
  simp only [sucRelabel] at large
  exact throughMiddle (d.relabel j) (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j)
    old oldTerms oldArgs next nextTerms nextArgs prev small large

private theorem atNext (d D H K M : OTerm α)
    (ih : Nonempty (Derivation body Γ (allLower D H K M)))
    (weak : Nonempty (Derivation body Γ (ltF d (suc (suc D))))) :
    Nonempty (Derivation body Γ (depthAt d (suc D) H K M)) := by
  obtain ⟨split⟩ := splitWeak d (suc D) weak
  let L := ltF d (suc D)
  let R := eqn d (suc D)
  obtain ⟨earlier⟩ := earlierAtNext (body := body) (Γ := L :: Γ) d D H K M (withHyp ih L)
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨same⟩ := equalDepth (body := body) (Γ := R :: Γ) d (suc D) H K M
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction earlier)
    (Derivation.implicationIntroduction same)⟩

theorem lowerAtSuccessor (D H K M : OTerm α)
    (ih : Nonempty (Derivation body Γ (allLower D H K M))) :
    Nonempty (Derivation body Γ (allLower (suc D) H K M)) := by
  apply buildLower (suc D) H K M
  intro β j Δ d keep weak
  have previous := renameInto ih j Δ keep
  rw [lowerRename] at previous
  simp only [sucRelabel] at weak ⊢
  exact atNext d (D.relabel j) (H.relabel j) (K.relabel j) (M.relabel j) previous weak

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverSelectedGrammarWeakDepthStepProof
