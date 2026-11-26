module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowMotiveProof
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalListCodecSupportProof
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
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

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

-- The physical equality test rejects each strict arm of genuine arithmetic trichotomy.
theorem nonzeroEquality (h k : OTerm α) (hit : Derivation body Γ (missGraph h k).not) :
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


open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePassWindowTargets (windowAt allWindow)
open NumberedWindowInternalSparsePassWindowSyntaxProof (windowRename moveGuard)

private theorem atSingleMember (W : Program 3) (ctx ty code seed k : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code seed z)))
    (guard : Nonempty (Derivation body Γ (windowAt W ctx ty seed)))
    (member : Nonempty (Derivation body Γ (memberGraph code k))) :
    Nonempty (Derivation body Γ (windowAt W ctx ty k)) := by
  obtain ⟨split⟩ := consInversion code seed z k cell member
  obtain ⟨guard⟩ := guard
  let P := (missGraph seed k).not
  let Q := memberGraph z k
  obtain ⟨e⟩ := nonzeroEquality (body := body) (Γ := P :: Γ) seed k (Derivation.hypothesis List.mem_cons_self)
  obtain ⟨yes⟩ := moveGuard W ctx ty seed k e (addHyp guard P)
  have nilRun := nilRecover (body := body) (Gamma := Q :: Γ) memberBase memberStep (suc z)
    (![k] : Fin 1 → OTerm α) ⟨Derivation.hypothesis List.mem_cons_self⟩
  obtain ⟨impossible⟩ := valueUnique memberBase (suc z) z (![k] : Fin 1 → OTerm α) nilRun (zeroConstantValue _)
  exact ⟨disjunctionElimination split (Derivation.implicationIntroduction yes)
    (Derivation.implicationIntroduction (Derivation.explosion (sucNeZeroApply impossible)))⟩

theorem singletonWindow (W : Program 3) (ctx ty code seed : OTerm α)
    (cell : Nonempty (Derivation body Γ (consGraph code seed z)))
    (guard : Nonempty (Derivation body Γ (windowAt W ctx ty seed))) :
    Nonempty (Derivation body Γ (allWindow W ctx ty code)) := by
  let j : α → α ⊕ Fin 1 := Sum.inl
  let k : OTerm (α ⊕ Fin 1) := .var (.inr 0)
  let B := memberGraph (code.relabel j) k
  let Δ := B :: Γ.map weaken
  have keep (p : Formula α) (hp : p ∈ Γ) : p.relabel j ∈ Δ :=
    List.mem_cons_of_mem _ (List.mem_map.mpr ⟨p,hp,rfl⟩)
  have c := renameInto cell j Δ keep
  rw [consGraphRename,ID1Completion.InternalTagArithmeticSyntaxProof.zRelabel] at c
  have g := renameInto guard j Δ keep
  rw [windowRename] at g
  obtain ⟨ok⟩ := atSingleMember W _ _ _ _ k c g ⟨Derivation.hypothesis List.mem_cons_self⟩
  exact ⟨Derivation.universalIntroduction (Derivation.implicationIntroduction ok)⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRoundWindowSingletonProof
