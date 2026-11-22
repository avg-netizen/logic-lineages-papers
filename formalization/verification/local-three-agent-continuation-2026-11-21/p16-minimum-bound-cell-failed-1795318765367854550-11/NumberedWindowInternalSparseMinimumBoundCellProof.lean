module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundWitnessProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumOrderChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphChoiceProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundCellProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalRawListRecursionProof (consValue)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (refl)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalApplicationValidityStackAppendInductionCoreProof (formulaCases)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseOrderedMinimum (minimumStep scratchMinimum)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseMinimumOrderTargets (update)
open NumberedWindowInternalSparseMinimumOrderChecks
open NumberedWindowInternalSparseMinimumBoundTargets
open NumberedWindowInternalSparseMinimumBoundSyntaxProof (witnessRename)
open NumberedWindowInternalSparseMinimumBoundWitnessProof (enter irrefl restrict)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem atCell (code h t prior k winner : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code h t)))
    (tail : Nonempty (Derivation body Γ (unary scratchMinimum prior t)))
    (step : Nonempty (Derivation body Γ (update h prior winner)))
    (bound : Nonempty (Derivation body Γ (ltF k winner).not)) :
    Nonempty (Derivation body Γ (boundedWitness code k)) := by
  have computed := consValue (constantZero 0) minimumStep code h t prior (suc winner)
    (Fin.elim0 : Fin 0 → OTerm α) cell tail step
  obtain ⟨computed⟩ := computed
  obtain ⟨bound⟩ := bound
  exact enter code k winner ⟨Derivation.conjunctionIntroduction computed bound⟩

private theorem withPrior (code h t p k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code h t)))
    (tail : Nonempty (Derivation body Γ (unary scratchMinimum (suc p) t)))
    (headBound : Derivation body (ltF h p :: Γ) (ltF k h).not)
    (tailBound : Derivation body ((ltF h p).not :: Γ) (ltF k p).not) :
    Nonempty (Derivation body Γ (boundedWitness code k)) := by
  obtain ⟨cell⟩ := cell
  obtain ⟨tail⟩ := tail
  let L := ltF h p
  apply formulaCases L _
  · obtain ⟨law⟩ := exact_OpenMinimumOrderedUpdate body α (L :: Γ) h p h
    have eqv := Derivation.implicationElimination (Derivation.conjunctionLeft law)
      (Derivation.hypothesis List.mem_cons_self)
    have actual := Derivation.implicationElimination (Derivation.conjunctionRight eqv) (refl h)
    exact atCell code h t (suc p) k h ⟨addHyp cell L⟩ ⟨addHyp tail L⟩ ⟨actual⟩ ⟨headBound⟩
  · obtain ⟨law⟩ := exact_OpenMinimumOrderedUpdate body α (L.not :: Γ) h p p
    have eqv := Derivation.implicationElimination (Derivation.conjunctionRight law)
      (Derivation.hypothesis List.mem_cons_self)
    have actual := Derivation.implicationElimination (Derivation.conjunctionRight eqv) (refl p)
    exact atCell code h t (suc p) k p ⟨addHyp cell L.not⟩ ⟨addHyp tail L.not⟩ ⟨actual⟩ ⟨tailBound⟩

theorem atHead (code h t : OTerm α) (cell : Nonempty (Derivation body Γ (consGraph code h t))) :
    Nonempty (Derivation body Γ (boundedWitness code h)) := by
  apply optionGraphCases scratchMinimum ![t] _
  · intro β j Δ keep nilTail
    rw [witnessRename]
    have hc := renameInto cell j Δ keep
    rw [consGraphRename] at hc
    obtain ⟨law⟩ := exact_OpenMinimumEmptyUpdate body β Δ (h.relabel j) (h.relabel j)
    have step := Derivation.implicationElimination (Derivation.conjunctionRight law) (refl _)
    apply atCell _ _ _ z _ _ hc _ ⟨step⟩ (irrefl _)
    exact nilTail
  · intro β j Δ p keep priorTail
    rw [witnessRename]
    have hc := renameInto cell j Δ keep
    rw [consGraphRename] at hc
    obtain ⟨hi⟩ := irrefl (body := body) (Γ := ltF (h.relabel j) p :: Δ) (h.relabel j)
    apply withPrior _ _ _ p _ hc _ hi (Derivation.hypothesis List.mem_cons_self)
    exact priorTail

theorem atTail (code h t k p : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code h t)))
    (row : Nonempty (Derivation body Γ (boundedRow t k p))) :
    Nonempty (Derivation body Γ (boundedWitness code k)) := by
  obtain ⟨row⟩ := row
  have bound := Derivation.conjunctionRight row
  let L := ltF h p
  obtain ⟨newBound⟩ := restrict (body := body) (Γ := L :: Γ) k h p (addHyp bound L)
    (Derivation.hypothesis List.mem_cons_self)
  exact withPrior code h t p k cell ⟨Derivation.conjunctionLeft row⟩ newBound (addHyp bound L.not)

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundCellProof
