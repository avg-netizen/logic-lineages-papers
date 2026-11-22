module

public import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenDataProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseDecodeSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLeastNumberProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaBoundaryProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAdditionLawsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenProof
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
open NumberedWindowInternalCoverAscendingRangeOpenDataProof (build recover afterStep)
open NumberedWindowInternalCoverAscendingRangeSyntaxProof (atRename atSubst testRename)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem zeroRule (i : OTerm α) :
    Nonempty (Derivation body Γ (atBound z i)) := by
  obtain ⟨empty⟩ := actualNothingBelowZero body α i
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion
    (Derivation.implicationElimination (weakenClosed empty (ltF i z :: Γ))
      (Derivation.hypothesis List.mem_cons_self)))⟩

private theorem fromPrevious (bound i previous : OTerm α)
    (old : Nonempty (Derivation body Γ (rangeReport previous bound)))
    (split : Nonempty (Derivation body Γ (ltF i bound ⊔ eqn i bound)))
    (ih : Nonempty (Derivation body Γ (atBound bound i))) :
    Nonempty (Derivation body Γ (rangeTest (suc bound) i)) := by
  apply programCases ascendingRange ![suc bound] _
  intro β j Δ out keep actual
  simp only [unaryInputsRename,sucRelabel] at actual
  rw [testRename,sucRelabel]
  have prior := renameInto old j Δ keep
  have s := renameInto split j Δ keep
  have h := renameInto ih j Δ keep
  rw [unaryRename] at prior
  rw [supRename,orderRename,eqnRelabel] at s
  rw [atRename] at h
  exact build (suc (bound.relabel j)) out (i.relabel j) actual
    (afterStep (bound.relabel j) (previous.relabel j) out (i.relabel j) prior actual s h)

private theorem succRule (bound i : OTerm α)
    (ih : Nonempty (Derivation body Γ (atBound bound i))) :
    Nonempty (Derivation body Γ (atBound (suc bound) i)) := by
  let L := ltF i (suc bound)
  let Δ := L :: Γ
  obtain ⟨compare⟩ := actualRightSuccessorSplit body α i bound
  rw [onEquality] at compare
  have split : Nonempty (Derivation body Δ (ltF i bound ⊔ eqn i bound)) :=
    ⟨Derivation.implicationElimination (weakenClosed compare Δ)
      (Derivation.hypothesis List.mem_cons_self)⟩
  have old := ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof.withHyp ih L
  have h : Nonempty (Derivation body Δ (rangeTest (suc bound) i)) := by
    apply programCases ascendingRange ![bound] _
    intro β j Θ previous keep run
    rw [testRename,sucRelabel]
    simp only [unaryInputsRename] at run
    have s := renameInto split j Θ keep
    have h := renameInto old j Θ keep
    rw [supRename,orderRename,eqnRelabel] at s
    rw [atRename] at h
    exact fromPrevious (bound.relabel j) (i.relabel j) previous run s h
  obtain ⟨h⟩ := h
  exact ⟨Derivation.implicationIntroduction h⟩

private theorem allBound (bound i : OTerm α) :
    Nonempty (Derivation body Γ (atBound bound i)) := by
  let θ := motive i
  have hb : Derivation body Γ (instantiate θ (emb z)) := by
    simp only [θ,motive,instantiate,bindEmbedding,atSubst,liftBind,varBind]
    exact Classical.choice (zeroRule i)
  have hs : Derivation body (θ :: Γ.map weaken) (successorInstance θ) := by
    simp only [θ,motive,successorInstance,nextEmbedding,atSubst,liftNext,varNext]
    exact Classical.choice (succRule (.var (.inr 0)) (i.relabel Sum.inl)
      ⟨Derivation.hypothesis List.mem_cons_self⟩)
  have result := Derivation.universalElimination (emb bound) (natInduction θ hb hs)
  simpa only [θ,motive,instantiate,bindEmbedding,atSubst,liftBind,varBind] using (Nonempty.intro result)

theorem exact_OpenCoverAscendingRangeMember : ExactOpenCoverAscendingRangeMember := by
  intro body α Γ out bound i run lower
  obtain ⟨r⟩ := allBound (body := body) (Γ := Γ) bound i
  obtain ⟨lower⟩ := lower
  exact recover bound out i run ⟨Derivation.implicationElimination r lower⟩

#print axioms exact_OpenCoverAscendingRangeMember

end LogicLineages.PersistentMarking.NumberedWindowInternalCoverAscendingRangeOpenProof
