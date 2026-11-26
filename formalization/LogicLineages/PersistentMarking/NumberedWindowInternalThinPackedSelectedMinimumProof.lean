module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseMinimumBoundChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBetaTotalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedSelectedMinimumProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (successorBranchIntro successorBranchElim zeroBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalControlGraphSupportProof (compositionValue valueUnique programRename)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSyntaxProof (z suc)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalBetaTotalityProof (addHyp)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalOriginalOrderSyntaxProof (ltF orderRename)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalFreshProbeProof (optionGraphCases)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseScratchMembershipOpenSyntaxProof (graphRename)
open NumberedWindowInternalSparsePathEnvelopeTargets (unary)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparseScratchMembershipTargets (memberGraph)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed minimumAtMembers packedLeastProgram)
open NumberedWindowInternalSparsePackedLeastOpen (leastGraph)
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (leastRename)
open NumberedWindowInternalSparsePackedBoundTargets
open NumberedWindowInternalSparsePackedBoundChecks (exact_OpenPackedPoolMinimum)
open NumberedWindowInternalSparseScratchMembershipOpenChecks (exact_OpenScratchMinimumOccurs)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)

@[expose] def ExactSelectedInSuppliedPool : Prop :=
  ∀ (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (body : Positive (Fin 1)) (α : Type) (Γ : List (Formula α)) (ctx ty seed pool minimum : OTerm α),
    Nonempty (Derivation body Γ ((programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed] ⊓
      leastGraph C X W s ctx ty seed minimum).imp (memberGraph pool minimum)))

theorem selected : ExactSelectedInSuppliedPool := by
  intro C X W s body α Γ ctx ty seed pool minimum
  let tape := ![ctx,ty,seed]
  let A := programGraph (membersAtSeed C X W s) pool tape ⊓ leastGraph C X W s ctx ty seed minimum
  let Δ := A :: Γ
  have input : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have given := Derivation.conjunctionRight input
  have members := Derivation.conjunctionLeft input
  have bound : Nonempty (Derivation body Δ (memberGraph pool minimum)) := by
    apply optionGraphCases contextOption (![ctx,ty,seed] : Fin 3 → OTerm α) _
    · intro β j Θ keep zero
      rw [tripleInputsRename] at zero
      have result := renameInto ⟨given⟩ j Θ keep
      rw [leastRename] at result
      let xs := ![ctx.relabel j,ty.relabel j,seed.relabel j]
      have absent := zeroBranchElim contextOption (constantZero 3) (minimumAtMembers C X W s)
        (suc (minimum.relabel j)) xs zero result
      obtain ⟨e⟩ := valueUnique (constantZero 3) (suc (minimum.relabel j)) z xs absent (zeroConstantValue xs)
      exact ⟨Derivation.explosion (sucNeZeroApply e)⟩
    · intro β j Θ payload keep known
      rw [tripleInputsRename] at known
      have result := renameInto ⟨given⟩ j Θ keep
      rw [leastRename] at result
      have suppliedPool := renameInto ⟨members⟩ j Θ keep
      simp only [programRename,tape,tripleInputsRename] at suppliedPool
      obtain ⟨result⟩ := result
      obtain ⟨suppliedPool⟩ := suppliedPool
      obtain ⟨known⟩ := known
      obtain ⟨law⟩ := exact_OpenPackedPoolMinimum C X W s body β Θ (ctx.relabel j) (ty.relabel j)
        (seed.relabel j) payload (pool.relabel j) (suc (minimum.relabel j))
      have minRun := Derivation.implicationElimination (Derivation.conjunctionLeft
        (Derivation.implicationElimination law (Derivation.conjunctionIntroduction known suppliedPool))) result
      obtain ⟨hit⟩ := exact_OpenScratchMinimumOccurs body β Θ (pool.relabel j) (minimum.relabel j)
      rw [graphRename]
      exact ⟨Derivation.implicationElimination hit minRun⟩
  obtain ⟨done⟩ := bound
  exact ⟨Derivation.implicationIntroduction done⟩

#print axioms selected
end LogicLineages.PersistentMarking.NumberedWindowInternalThinPackedSelectedMinimumProof
