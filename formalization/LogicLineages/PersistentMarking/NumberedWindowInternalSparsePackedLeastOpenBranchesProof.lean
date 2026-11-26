module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenSyntaxProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParserOpenSyntaxProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalControlGraphSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionFunctionalityProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSyntaxProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenBranchesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (valueUnique programRename)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (programCompositionCases)
open ID1Completion.InternalGraphCompositionFunctionalityProof (renameInto)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open ID1Completion.InternalTagArithmeticSyntaxProof (sucRelabel)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalSparseFieldParserOpenSyntaxProof (tripleInputsRename)
open NumberedWindowInternalSparseOrderedMinimum (scratchMinimum)
open NumberedWindowInternalSparsePackedLeast (contextOption membersAtSeed minimumAtMembers)
open NumberedWindowInternalSparseScratchMembershipOpenChecks (exact_OpenScratchMinimumOccurs)
open NumberedWindowInternalSparsePackedLeastOpen
open NumberedWindowInternalSparsePackedLeastOpenSyntaxProof (occurrenceRename occurrenceIntro)

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual zero context branch is the actual constant-zero program.
Its output cannot equal the observed successor on the same tape. -/
theorem reject (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected : OTerm α)
    (missing : Nonempty (Derivation body Γ (programGraph contextOption z ![ctx,ty,seed])))
    (accepted : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed selected))) :
    Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed selected)) := by
  have lost := zeroBranchElim contextOption (constantZero 3) (minimumAtMembers C X W s)
    (suc selected) (![ctx,ty,seed] : Fin 3 → OTerm α) missing accepted
  obtain ⟨impossible⟩ := valueUnique (constantZero 3) (suc selected) z
    (![ctx,ty,seed] : Fin 3 → OTerm α) lost
    (zeroConstantValue (![ctx,ty,seed] : Fin 3 → OTerm α))
  exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩

/-- The observed successor context tag selects the actual minimum branch.
Inverting its literal composition exposes the members output on the same
tape as an object eigenvariable; the checked scratch law gives occurrence. -/
theorem present (C : Program 3) (X : Program 2) (W : Program 3) (s : Settings)
    (ctx ty seed selected payload : OTerm α)
    (known : Nonempty (Derivation body Γ
      (programGraph contextOption (suc payload) ![ctx,ty,seed])))
    (accepted : Nonempty (Derivation body Γ (leastGraph C X W s ctx ty seed selected))) :
    Nonempty (Derivation body Γ (poolOccurrence C X W s ctx ty seed selected)) := by
  have selectedBranch := successorBranchElim contextOption (constantZero 3)
    (minimumAtMembers C X W s) (suc selected) payload
    (![ctx,ty,seed] : Fin 3 → OTerm α) known accepted
  apply programCompositionCases scratchMinimum (fun _ : Fin 1 => membersAtSeed C X W s)
    (suc selected) (![ctx,ty,seed] : Fin 3 → OTerm α)
    (poolOccurrence C X W s ctx ty seed selected) selectedBranch
  intro β j ys Δ keep minimum pooledAll
  rw [occurrenceRename]
  have tagged := renameInto known j Δ keep
  rw [programRename,tripleInputsRename,sucRelabel] at tagged
  have pooled := pooledAll 0
  rw [tripleInputsRename] at pooled
  rw [sucRelabel] at minimum
  have tuple : (![ys 0] : Fin 1 → OTerm β) = ys := by
    funext i
    obtain rfl := Fin.eq_zero i
    rfl
  have least : Nonempty (Derivation body Δ
      (programGraph scratchMinimum (suc (selected.relabel j))
        (![ys 0] : Fin 1 → OTerm β))) := by
    rw [tuple]
    exact minimum
  obtain ⟨ofMinimum⟩ := exact_OpenScratchMinimumOccurs body β Δ (ys 0) (selected.relabel j)
  obtain ⟨minimumAt⟩ := least
  obtain ⟨taggedAt⟩ := tagged
  obtain ⟨pooledAt⟩ := pooled
  exact occurrenceIntro C X W s (ctx.relabel j) (ty.relabel j) (seed.relabel j)
    (selected.relabel j) (payload.relabel j) (ys 0)
    ⟨Derivation.conjunctionIntroduction taggedAt
      (Derivation.conjunctionIntroduction pooledAt
        (Derivation.implicationElimination ofMinimum minimumAt))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastOpenBranchesProof
