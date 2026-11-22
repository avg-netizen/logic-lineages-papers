module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundTargets
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
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundChecks
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

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}
variable (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)

private theorem atKnown (ctx ty seed payload pool out : OTerm α)
    (known : Nonempty (Derivation body Γ (programGraph contextOption (suc payload) ![ctx,ty,seed])))
    (members : Nonempty (Derivation body Γ (programGraph (membersAtSeed C X W s) pool ![ctx,ty,seed])))
    (actual : Nonempty (Derivation body Γ (programGraph (packedLeastProgram C X W s) out ![ctx,ty,seed]))) :
    Nonempty (Derivation body Γ (unary scratchMinimum out pool)) := by
  have selected := successorBranchElim contextOption (constantZero 3) (minimumAtMembers C X W s)
    out payload ![ctx,ty,seed] known actual
  apply compositionRecover scratchMinimum (fun _ : Fin 1 => membersAtSeed C X W s)
    out ![ctx,ty,seed] ![pool] selected
  intro i
  obtain rfl := Fin.eq_zero i
  exact members

theorem exact_OpenPackedPoolMinimum : ExactOpenPackedPoolMinimum := by
  intro C X W s body α Γ ctx ty seed payload pool out
  let tape := ![ctx,ty,seed]
  let A := programGraph contextOption (suc payload) tape ⊓ programGraph (membersAtSeed C X W s) pool tape
  let L := programGraph (packedLeastProgram C X W s) out tape
  let M := unary scratchMinimum out pool
  have d : Derivation body (A :: Γ) A := Derivation.hypothesis List.mem_cons_self
  have c := Derivation.conjunctionLeft d
  have m := Derivation.conjunctionRight d
  obtain ⟨forward⟩ := atKnown (body := body) (Γ := L :: A :: Γ) C X W s ctx ty seed payload pool out
    ⟨addHyp c L⟩ ⟨addHyp m L⟩ ⟨Derivation.hypothesis List.mem_cons_self⟩
  have branch : Nonempty (Derivation body (M :: A :: Γ) (programGraph (minimumAtMembers C X W s) out tape)) := by
    apply compositionValue scratchMinimum (fun _ : Fin 1 => membersAtSeed C X W s)
      out tape ![pool] ⟨Derivation.hypothesis List.mem_cons_self⟩
    intro i
    obtain rfl := Fin.eq_zero i
    exact ⟨addHyp m M⟩
  obtain ⟨reverse⟩ := successorBranchIntro contextOption (constantZero 3) (minimumAtMembers C X W s)
    out payload tape ⟨addHyp c M⟩ branch
  exact ⟨Derivation.implicationIntroduction (Derivation.conjunctionIntroduction
    (Derivation.implicationIntroduction forward) (Derivation.implicationIntroduction reverse))⟩

theorem exact_OpenPackedLeastLowerBound : ExactOpenPackedLeastLowerBound := by
  intro C X W s body α Γ ctx ty seed pool candidate minimum
  let tape := ![ctx,ty,seed]
  let A := leastGraph C X W s ctx ty seed minimum ⊓
    (programGraph (membersAtSeed C X W s) pool tape ⊓ memberGraph pool candidate)
  let Δ := A :: Γ
  have input : Derivation body Δ A := Derivation.hypothesis List.mem_cons_self
  have given := Derivation.conjunctionLeft input
  have supplied := Derivation.conjunctionRight input
  have members := Derivation.conjunctionLeft supplied
  have hit := Derivation.conjunctionRight supplied
  have bound : Nonempty (Derivation body Δ (ltF candidate minimum).not) := by
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
      have retained := renameInto ⟨hit⟩ j Θ keep
      rw [graphRename] at retained
      obtain ⟨minRun⟩ := atKnown C X W s _ _ _ payload _ (suc (minimum.relabel j)) known suppliedPool result
      obtain ⟨retained⟩ := retained
      obtain ⟨law⟩ := NumberedWindowInternalSparseMinimumBoundChecks.exact_OpenScratchMinimumLowerBound
        body β Θ (pool.relabel j) (candidate.relabel j) (minimum.relabel j)
      change Nonempty (Derivation body Θ ((ltF candidate minimum).relabel j).not)
      rw [orderRename]
      exact ⟨Derivation.implicationElimination law (Derivation.conjunctionIntroduction minRun retained)⟩
  obtain ⟨bound⟩ := bound
  exact ⟨Derivation.implicationIntroduction bound⟩

#print axioms exact_OpenPackedPoolMinimum
#print axioms exact_OpenPackedLeastLowerBound
end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedBoundChecks
