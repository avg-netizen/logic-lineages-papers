module
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipOpenChecks
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceBranchProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestPredecessorProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalLessThanSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTagArithmeticSupportProof

public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceOpenBranchesProof
open FirstOrder Language
open LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue valueUnique)
open ID1Completion.InternalAcceptance (constantZero)
open ID1Completion.InternalAcceptanceBranchProof (zeroBranchElim successorBranchElim)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalEqualityTest (predecessor)
open ID1Completion.InternalEqualityTestPredecessorProof (predecessorSuccessor)
open ID1Completion.InternalLessThanSupportProof (zeroConstantValue)
open ID1Completion.InternalTagArithmeticSupportProof (sucNeZeroApply)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z unary)
open NumberedWindowInternalSparseFieldParser (parser)
open NumberedWindowInternalSparseFieldParserTargets (parserGraph)
open NumberedWindowInternalSparseOrderedMinimum
open NumberedWindowInternalSparseScratchMembershipOpenChecks (exact_OpenScratchMinimumOccurs)
open NumberedWindowInternalSparseRawMinimumOccurrence

attribute [local irreducible] programGraph

variable {body : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

/-- The actual zero parser branch is the actual constant-zero minimum.
It cannot coexist with the observed successor output at this raw tape. -/
theorem reject (raw selected : OTerm α)
    (missing : Nonempty (Derivation body Γ (parserGraph z raw)))
    (accepted : Nonempty (Derivation body Γ (rawMinimumGraph raw selected))) :
    Nonempty (Derivation body Γ (parsedOccurrence raw selected)) := by
  have lost := zeroBranchElim parser (constantZero 1) parsedMinimum (suc selected)
    (![raw] : Fin 1 → OTerm α) missing accepted
  obtain ⟨impossible⟩ := valueUnique (constantZero 1) (suc selected) z
    (![raw] : Fin 1 → OTerm α) lost (zeroConstantValue ![raw])
  exact ⟨Derivation.explosion (sucNeZeroApply impossible)⟩

private theorem sameDecoded (raw scratch : OTerm α)
    (known : Nonempty (Derivation body Γ (parserGraph (suc scratch) raw))) :
    Nonempty (Derivation body Γ (unary decodedScratch scratch raw)) := by
  apply compositionValue predecessor (fun _ : Fin 1 => parser) scratch
    (![raw] : Fin 1 → OTerm α) (![suc scratch] : Fin 1 → OTerm α)
    (predecessorSuccessor scratch)
  intro i
  obtain rfl := Fin.eq_zero i
  exact known

/-- The observed parser successor gives exactly its own predecessor as
scratch input to the real selected minimum; no numerical decode is read. -/
theorem present (raw scratch selected : OTerm α)
    (known : Nonempty (Derivation body Γ (parserGraph (suc scratch) raw)))
    (accepted : Nonempty (Derivation body Γ (rawMinimumGraph raw selected))) :
    Nonempty (Derivation body Γ (parsedOccurrenceRow raw scratch selected)) := by
  have selectedBranch := successorBranchElim parser (constantZero 1) parsedMinimum
    (suc selected) scratch (![raw] : Fin 1 → OTerm α) known accepted
  have actual : Nonempty (Derivation body Γ (unary scratchMinimum (suc selected) scratch)) := by
    apply compositionRecover scratchMinimum (fun _ : Fin 1 => decodedScratch) (suc selected)
      (![raw] : Fin 1 → OTerm α) (![scratch] : Fin 1 → OTerm α) selectedBranch
    intro i
    obtain rfl := Fin.eq_zero i
    exact sameDecoded raw scratch known
  obtain ⟨ofMin⟩ := exact_OpenScratchMinimumOccurs body α Γ scratch selected
  obtain ⟨min⟩ := actual
  obtain ⟨parsed⟩ := known
  exact ⟨Derivation.conjunctionIntroduction parsed
    (Derivation.conjunctionIntroduction min (Derivation.implicationElimination ofMin min))⟩

end LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawMinimumOccurrenceOpenBranchesProof
