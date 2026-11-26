module

public import LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathAdvanceOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceOpenProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalTagArithmeticSyntaxProof (eqn zRelabel eqnRelabel)
open ID1Completion.InternalTagArithmeticSupportProof
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof
  (zeroBranchElim zeroBranchIntro successorBranchElim successorBranchIntro)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (programRename valueUnique)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowInternalSparsePathEnvelopeTargets (z)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalZeroRankAdvance (resultRank zeroOutput)
open NumberedWindowInternalSparsePathAdvance (advance)
open NumberedWindowInternalSparsePathAdvanceOpenChecks (exact_OpenNoCurrent)

attribute [local irreducible] programGraph

variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem notRename {β : Type} (f : Formula α) (j : α → β) :
    f.not.relabel j = (f.relabel j).not := rfl

/-- If the actual filtered callback returned a present encoding, its
held result is also an output of the unchanged ordinary callback. -/
theorem exact_OpenFilteredAdvanceLive {n : Nat} (g : Program 1) (A : Program n)
    (out : OTerm α) (xs : Fin n → OTerm α)
    (held : Nonempty (Derivation B Γ (programGraph (zeroOutput g A) out xs)))
    (live : Nonempty (Derivation B Γ (eqn out z).not)) :
    Nonempty (Derivation B Γ (programGraph A out xs)) := by
  apply optionGraphCases (resultRank g A) xs _
  · intro β j Δ keep zero
    rw [programRename]
    have carried := renameInto held j Δ keep
    rw [programRename] at carried
    exact zeroBranchElim (resultRank g A) A (constantZero n) (out.relabel j) _ zero carried
  · intro β j Δ k keep nonzero
    have carried := renameInto held j Δ keep
    rw [programRename] at carried
    let ys := fun i => (xs i).relabel j
    have rejected := successorBranchElim (resultRank g A) A (constantZero n)
      (out.relabel j) k ys nonzero carried
    obtain ⟨e⟩ := valueUnique (constantZero n) (out.relabel j) z ys rejected (constantZeroValue ys)
    obtain ⟨notZero⟩ := renameInto live j Δ keep
    have bad : Derivation B Δ ((eqn (out.relabel j) z).not) := by
      simpa only [notRename,eqnRelabel,zRelabel] using notZero
    exact ⟨Derivation.explosion (Derivation.implicationElimination bad e)⟩

/-- An ordinary zero is still zero after filtering, regardless of the
result-rank computation. This is a derivation in the object calculus. -/
theorem exact_OpenFilteredAdvanceKeepsZero {n : Nat} (g : Program 1) (A : Program n)
    (xs : Fin n → OTerm α)
    (dead : Nonempty (Derivation B Γ (programGraph A z xs))) :
    Nonempty (Derivation B Γ (programGraph (zeroOutput g A) z xs)) := by
  apply optionGraphCases (resultRank g A) xs _
  · intro β j Δ keep zero
    simp only [programRename,zRelabel]
    have carried := renameInto dead j Δ keep
    simp only [programRename,zRelabel] at carried
    exact zeroBranchIntro (resultRank g A) A (constantZero n) z _ zero carried
  · intro β j Δ k keep nonzero
    simp only [programRename,zRelabel]
    exact successorBranchIntro (resultRank g A) A (constantZero n) z k _ nonzero (constantZeroValue _)

theorem exact_OpenFilteredAdvanceDead (g : Program 1) (raw : Program 5) (least : Program 3)
    (ctx ty hop : OTerm α) :
    Nonempty (Derivation B Γ (programGraph (zeroOutput g (advance raw least)) z ![ctx,ty,z,hop])) := by
  obtain ⟨ordinary⟩ := exact_OpenNoCurrent B raw least α ctx ty hop
  exact exact_OpenFilteredAdvanceKeepsZero g (advance raw least) ![ctx,ty,z,hop]
    ⟨Derivation.weakening (fun _ h => False.elim (List.not_mem_nil h)) ordinary⟩

#print axioms exact_OpenFilteredAdvanceLive
#print axioms exact_OpenFilteredAdvanceKeepsZero
#print axioms exact_OpenFilteredAdvanceDead
end LogicLineages.PersistentMarking.NumberedWindowInternalZeroRankAdvanceOpenProof
