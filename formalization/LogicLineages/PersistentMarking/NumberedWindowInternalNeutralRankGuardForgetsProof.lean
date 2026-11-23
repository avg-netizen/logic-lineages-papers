module
public import LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowComputabilityFormulaTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardForgetsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators
open ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalControlGraphSupportProof (programRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel zRelabel)
open ID1Completion.InternalAcceptance (branch conjunction)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowComputabilityFormulaTargets (accepts)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalAtomicRefinement (atSource atTarget)
open NumberedWindowInternalNeutralRankGuard

private theorem acceptsGraph {α : Type} (p : Program 3) (x w y : OTerm α) :
    accepts p x w y = programGraph p (suc z) ![x,w,y] := rfl

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

private theorem oldAcceptance (g : Program 1) (p checks : Program 3) (x w y : OTerm α)
    (h : Nonempty (Derivation B Γ
      (programGraph (branch (atSource g) p (conjunction p checks)) (suc z) ![x,w,y]))) :
    Nonempty (Derivation B Γ (programGraph p (suc z) ![x,w,y])) := by
  apply optionGraphCases (atSource g) (![x,w,y] : Fin 3 → OTerm α) _
  · intro β j Δ keep absent
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    rw [tripleInputsRename] at absent
    have a := renameInto h j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at a
    exact zeroBranchElim (atSource g) p (conjunction p checks) (suc z)
      ![x.relabel j,w.relabel j,y.relabel j] absent a
  · intro β j Δ k keep present
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel]
    rw [tripleInputsRename] at present
    have a := renameInto h j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel,zRelabel] at a
    let t : Fin 3 → OTerm β := ![x.relabel j,w.relabel j,y.relabel j]
    obtain ⟨seen⟩ := conjunctionRecover p checks t
      (successorBranchElim (atSource g) p (conjunction p checks) (suc z) k t present a)
    exact ⟨Derivation.conjunctionLeft seen⟩

/-- Same ambient body, same accepted numerical tape, original p retained.
This transfers only arithmetic, never I or typed proof derivations. -/
theorem exact_OpenRankApplicationForgets (i g : Program 1) (p : Program 3) (x w y : OTerm α)
    (h : Nonempty (Derivation B Γ (accepts (rankApplication i g p) x w y))) :
    Nonempty (Derivation B Γ (accepts p x w y)) := by
  rw [acceptsGraph] at h ⊢
  exact oldAcceptance g p (conjunction (targetHasRank g) (atTarget i)) x w y h

/-- The actual even guard likewise forgets only the extra arithmetic. -/
theorem exact_OpenRankEvenForgets (i g : Program 1) (r : Program 3) (x w y : OTerm α)
    (h : Nonempty (Derivation B Γ (accepts (rankEven i g r) x w y))) :
    Nonempty (Derivation B Γ (accepts r x w y)) := by
  rw [acceptsGraph] at h ⊢
  exact oldAcceptance g r (conjunction (targetHasRank g) (conjunction (atTarget i) (lowersRank g))) x w y h

#print axioms exact_OpenRankApplicationForgets
#print axioms exact_OpenRankEvenForgets
end LogicLineages.PersistentMarking.NumberedWindowInternalNeutralRankGuardForgetsProof
