module

public import LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastDefinitions
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePathEnvelopeTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalCoverRefinedPositiveUnitConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalRecursionGraphStepSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastReportsProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalLessThan (constantOne)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionRecover constantZeroValue)
open ID1Completion.InternalControlGraphSupportProof (valueUnique programRename)
open ID1Completion.InternalRecursionGraphStepSyntaxProof (conjunctionRename)
open ID1Completion.InternalTagArithmeticSyntaxProof (zRelabel sucRelabel)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram (Program)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalCoverRefinedPositiveUnitConjunctionProof (conjunctionUnitFromPositive)
open NumberedWindowInternalRankCheckedLeast

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- A positive physical result on the exact original tape keeps the
original positive least graph and the genuine unit rank equality test. -/
theorem exact_OpenRankCheckedLeastReports (g : Program 1) (L : Program 3)
    (ctx ty seed k : OTerm α)
    (checked : Nonempty (Derivation B Γ (programGraph (checkedLeast g L) (suc k) ![ctx,ty,seed]))) :
    Nonempty (Derivation B Γ
      (programGraph L (suc k) ![ctx,ty,seed] ⊓ programGraph (rankEq g L) (suc z) ![ctx,ty,seed])) := by
  let Q := programGraph L (suc k) ![ctx,ty,seed] ⊓ programGraph (rankEq g L) (suc z) ![ctx,ty,seed]
  let T := rankTest g L
  apply optionGraphCases T (![ctx,ty,seed] : Fin 3 → OTerm α) Q
  · intro β j Δ keep zero
    rw [tripleInputsRename] at zero
    have c := renameInto checked j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at c
    let ys : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have bad := zeroBranchElim T (constantZero 3) L (suc (k.relabel j)) ys zero c
    obtain ⟨impossible⟩ := valueUnique (constantZero 3) (suc (k.relabel j)) z ys bad (constantZeroValue ys)
    exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩
  · intro β j Δ m keep rank
    rw [tripleInputsRename] at rank
    have c := renameInto checked j Δ keep
    simp only [programRename,tripleInputsRename,sucRelabel] at c
    let ys : Fin 3 → OTerm β := ![ctx.relabel j,ty.relabel j,seed.relabel j]
    have old := successorBranchElim T (constantZero 3) L (suc (k.relabel j)) m ys rank c
    have one := conjunctionUnitFromPositive (rankEq g L) (constantOne 3) ys m rank
    obtain ⟨both⟩ := conjunctionRecover (rankEq g L) (constantOne 3) ys one
    obtain ⟨old⟩ := old
    simp only [Q,conjunctionRename,programRename,tripleInputsRename,sucRelabel,zRelabel]
    exact ⟨Derivation.conjunctionIntroduction old (Derivation.conjunctionLeft both)⟩

#print axioms exact_OpenRankCheckedLeastReports
end LogicLineages.PersistentMarking.NumberedWindowInternalRankCheckedLeastReportsProof
