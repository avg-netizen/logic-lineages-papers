module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundCellProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFilterInclusionMemberConsProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalQuotientComparisonProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRawListRecursionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalPositiveUnfoldingSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundRowsProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalListCodecSupportProof (consGraph consGraphRename)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF)
open ID1Completion.InternalQuotientComparisonProof (compareView actualOriginalComparison)
open ID1Completion.InternalEqualityTestProof (rejectForwardOrder rejectBackwardOrder)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique)
open ID1Completion.InternalRawListRecursionProof (nilRecover)
open ID1Completion.InternalBetaTotalityProof (addHyp disjunctionElimination)
open ID1Completion.InternalPositiveUnfoldingSupportProof (weakenClosed)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open NumberedWindowInternalSparseScratchMembership (memberBase memberStep)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparseFilterInclusionSyntaxProof (missGraph)
open NumberedWindowInternalSparseFilterInclusionMemberConsProof (consInversion)
open NumberedWindowInternalSparseMinimumBoundTargets
open NumberedWindowInternalSparseMinimumBoundSyntaxProof (memberBound witnessRename)
open NumberedWindowInternalSparseMinimumBoundWitnessProof (candidateTransport casesValue)
open NumberedWindowInternalSparseMinimumBoundCellProof (atHead atTail)

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

-- The physical equality test rejects each strict arm of genuine arithmetic trichotomy.
private theorem headEqual (h k : OTerm α) (hit : Derivation body Γ (missGraph h k).not) :
    Nonempty (Derivation body Γ (eqn h k)) := by
  obtain ⟨comparison⟩ := actualOriginalComparison body α h k
  have split := compareView (weakenClosed comparison Γ)
  let L := ltF h k
  let R := ltF k h
  let M := eqn h k
  obtain ⟨noLeft⟩ := rejectForwardOrder (body := body) (Gamma := L :: Γ) h k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨noRight⟩ := rejectBackwardOrder (body := body) (Gamma := R :: Γ) h k
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  have left : Derivation body Γ (L.imp M) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp hit L) noLeft))
  have right : Derivation body Γ (R.imp M) := Derivation.implicationIntroduction
    (Derivation.explosion (Derivation.implicationElimination (addHyp hit R) noRight))
  have same : Derivation body Γ (M.imp M) := Derivation.implicationIntroduction
    (Derivation.hypothesis List.mem_cons_self)
  exact ⟨disjunctionElimination split left (Derivation.implicationIntroduction
    (disjunctionElimination (Derivation.hypothesis List.mem_cons_self)
      (addHyp same (M ⊔ R)) (addHyp right (M ⊔ R))))⟩

theorem emptyBound (k : OTerm α) : Nonempty (Derivation body Γ (memberBound z k)) := by
  let A := memberGraph z k
  have hit : Nonempty (Derivation body (A :: Γ) A) := ⟨Derivation.hypothesis List.mem_cons_self⟩
  have nilRun := nilRecover memberBase memberStep (suc z) (![k] : Fin 1 → OTerm α) hit
  obtain ⟨absurd⟩ := valueUnique memberBase (suc z) z (![k] : Fin 1 → OTerm α)
    nilRun (zeroConstantValue _)
  exact ⟨Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply absurd))⟩

private theorem fromTail (code h t k : OTerm α) (cell : Nonempty (Derivation body Γ (consGraph code h t)))
    (tail : Nonempty (Derivation body Γ (boundedWitness t k))) :
    Nonempty (Derivation body Γ (boundedWitness code k)) := by
  apply casesValue t k _ tail
  intro β j Δ w keep row
  rw [witnessRename]
  have hc := renameInto cell j Δ keep
  rw [consGraphRename] at hc
  exact atTail _ _ _ _ w hc row

theorem consBound (code h t k : OTerm α) (cell : Nonempty (Derivation body Γ (consGraph code h t)))
    (ih : Nonempty (Derivation body Γ (memberBound t k))) :
    Nonempty (Derivation body Γ (memberBound code k)) := by
  obtain ⟨cell⟩ := cell
  obtain ⟨ih⟩ := ih
  let A := memberGraph code k
  let P := (missGraph h k).not
  let Q := memberGraph t k
  let Δ := A :: Γ
  obtain ⟨split⟩ := consInversion (body := body) (Γ := Δ) code h t k ⟨addHyp cell A⟩
    ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨e⟩ := headEqual (body := body) (Γ := P :: Δ) h k (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨head⟩ := candidateTransport code h k e
    (atHead code h t ⟨addHyp (addHyp cell A) P⟩)
  have old := Derivation.implicationElimination (addHyp (addHyp ih A) Q)
    (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨later⟩ := fromTail code h t k ⟨addHyp (addHyp cell A) Q⟩ ⟨old⟩
  exact ⟨Derivation.implicationIntroduction (disjunctionElimination split
    (Derivation.implicationIntroduction head) (Derivation.implicationIntroduction later))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundRowsProof
