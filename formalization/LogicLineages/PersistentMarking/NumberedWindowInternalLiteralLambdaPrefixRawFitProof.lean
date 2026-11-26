module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixRawFitProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalAcceptance (conjunction)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation)
open ID1Completion.InternalAcceptanceConjunctionProof (conjunctionAccept conjunctionRecover)
open NumberedWindowCopyAlgorithm (Entries)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualRawCalibration packedRaw)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowInternalSparsePathEnvelopeTargets (suc z)
open NumberedWindowInternalLiteralLambdaLexicalGateNumericProof (typedTape)
open NumberedWindowInternalLiteralLambdaPrefixMachineProof (prefixOwn)
open NumberedWindowInternalLiteralLambdaPrefixCalibrationProof (exact_LambdaPrefixCalibrated)
open NumberedWindowInternalLiteralRootDispatchOpenProof (D)

def prefixRaw (W : Program 3) (raw : Program 5) : Program 5 :=
  conjunction raw (prefixOwn W)

theorem exact_LambdaPrefixRawCalibration (s : Settings) (xs : Entries) (W : Program 3) (raw : Program 5)
    (wFit : ActualPackedWindow s W) (rawFit : ActualRawCalibration xs s raw) :
    ActualRawCalibration xs s (prefixRaw W raw) := by
  intro c t q w r
  change evaluate (prefixRaw W raw) (typedTape c t q w r) = _
  rw [prefixRaw,actualConjunctionEvaluation,rawFit c t q w r]
  cases h : packedRaw xs s c t q w r with
  | false => rfl
  | true =>
    have ok := exact_LambdaPrefixCalibrated W s wFit xs c t q w r h
    rw [ok]
    rfl

attribute [local irreducible] programGraph
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

theorem exact_OpenPrefixRaw (W : Program 3) (raw : Program 5) (xs : Fin 5 → OTerm α) :
    D B Γ (programGraph (prefixRaw W raw) (suc z) xs) ↔
    D B Γ (programGraph raw (suc z) xs) ∧ D B Γ (programGraph (prefixOwn W) (suc z) xs) := by
  constructor
  · intro a
    obtain ⟨h⟩ := conjunctionRecover raw (prefixOwn W) xs a
    exact ⟨⟨Derivation.conjunctionLeft h⟩,⟨Derivation.conjunctionRight h⟩⟩
  · rintro ⟨a,b⟩
    exact conjunctionAccept raw (prefixOwn W) xs a b

#print axioms exact_LambdaPrefixRawCalibration
#print axioms exact_OpenPrefixRaw
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralLambdaPrefixRawFitProof
