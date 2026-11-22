module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginChecks
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open ID1Completion.InternalAcceptanceSupportProof (programCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalSourceInversionSupportProof (onEquality)
open ID1Completion.InternalLeastNumberProof (actualRightSuccessorSplit actualNothingBelowZero)
open ID1Completion.InternalBetaBoundaryProof (supRename)
open ID1Completion.InternalTagArithmeticSyntaxProof
  (emb eqn eqnRelabel bindEmbedding liftBind varBind nextEmbedding sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (natInduction)
open ID1Completion.InternalAdditionLawsProof (liftNext varNext)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof (unaryRename)
open NumberedWindowInternalSparseDecodeSyntaxProof (unaryInputsRename)
open NumberedWindowInternalCoverAscendingRangeTargets
open NumberedWindowInternalCoverAscendingRangeOpenDataProof (build recover)
open NumberedWindowInternalCoverAscendingRangeOriginDataProof (nilHit afterStep)
open NumberedWindowInternalCoverAscendingRangeOriginTargets
open NumberedWindowInternalCoverAscendingRangeOriginSyntaxProof (backRename backSubst)
open ID1Completion.InternalControlGraphSupportProof (recursionZeroValue)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalAcceptance (constantZero)
open NumberedWindowInternalCoverAscendingRangeSyntaxProof (testRename)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem zeroRule (i : OTerm α) :
    Nonempty (Derivation body Γ (backBound z i)) := by
  let H := rangeTest z i
  let Δ := H :: Γ
  have run : Nonempty (Derivation body Δ (rangeReport z z)) :=
    recursionZeroValue (constantZero 0) rangeStep z Fin.elim0 (zeroConstantValue _)
  obtain ⟨bad⟩ := nilHit i
    (recover z z i run ⟨Derivation.hypothesis List.mem_cons_self⟩)
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion bad)⟩

private theorem fromPrevious (bound i previous : OTerm α)
    (old : Nonempty (Derivation body Γ (rangeReport previous bound)))
    (member : Nonempty (Derivation body Γ (rangeTest (suc bound) i)))
    (ih : Nonempty (Derivation body Γ (backBound bound i))) :
    Nonempty (Derivation body Γ (ltF i (suc bound))) := by
  apply programCases ascendingRange ![suc bound] _
  intro β j Δ out keep actual
  simp only [unaryInputsRename,sucRelabel] at actual
  rw [orderRename,sucRelabel]
  have prior := renameInto old j Δ keep
  have hit := renameInto member j Δ keep
  have h := renameInto ih j Δ keep
  change Nonempty (Derivation body Δ ((NumberedWindowInternalSparsePathEnvelopeTargets.unary
    ascendingRange previous bound).relabel j)) at prior
  rw [unaryRename] at prior
  rw [testRename,sucRelabel] at hit
  rw [backRename] at h
  have present := recover (suc (bound.relabel j)) out (i.relabel j) actual hit
  exact afterStep (bound.relabel j) (previous.relabel j) out (i.relabel j) prior actual present h

private theorem succRule (bound i : OTerm α)
    (ih : Nonempty (Derivation body Γ (backBound bound i))) :
    Nonempty (Derivation body Γ (backBound (suc bound) i)) := by
  let H := rangeTest (suc bound) i
  let Δ := H :: Γ
  have present : Nonempty (Derivation body Δ H) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have old := ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof.withHyp ih H
  have h : Nonempty (Derivation body Δ (ltF i (suc bound))) := by
    apply programCases ascendingRange ![bound] _
    intro β j Θ previous keep run
    rw [orderRename,sucRelabel]
    simp only [unaryInputsRename] at run
    have hit := renameInto present j Θ keep
    have h := renameInto old j Θ keep
    simp only [H,testRename,sucRelabel] at hit
    rw [backRename] at h
    exact fromPrevious (bound.relabel j) (i.relabel j) previous run hit h
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

private theorem allBound (bound i : OTerm α) :
    Nonempty (Derivation body Γ (backBound bound i)) := by
  let θ := backMotive i
  have hb : Derivation body Γ (instantiate θ (emb z)) := by
    simp only [θ,backMotive,instantiate,bindEmbedding,backSubst,liftBind,varBind]
    exact Classical.choice (zeroRule i)
  have hs : Derivation body (θ :: Γ.map weaken) (successorInstance θ) := by
    simp only [θ,backMotive,successorInstance,nextEmbedding,backSubst,liftNext,varNext]
    exact Classical.choice (succRule (.var (.inr 0)) (i.relabel Sum.inl)
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have result := Derivation.universalElimination (emb bound) (natInduction θ hb hs)
  simpa only [θ,backMotive,instantiate,bindEmbedding,backSubst,liftBind,varBind] using (Nonempty.intro result)

theorem exact_OpenCoverAscendingRangeOrigin : ExactOpenCoverAscendingRangeOrigin := by
  intro body α Γ out bound i run member
  obtain ⟨r⟩ := allBound (body := body) (Γ := Γ) bound i
  obtain ⟨hit⟩ := build bound out i run member
  exact ⟨Derivation.implicationElimination r hit⟩

#print axioms exact_OpenCoverAscendingRangeOrigin

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOriginChecks
