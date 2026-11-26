module
public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMixedLeastProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMixedCalibrationProof
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptanceCalibrationProof (evalBranch actualConjunctionEvaluation)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeTwo compositeThree)
open NumberedWindowInternalSparsePathAdvanceTargets (ActualLeastCalibration)
open NumberedWindowScalarAlgorithm (Settings)
open NumberedWindowInternalLiteralCoveredMemo (WindowSeedsCovered)
open NumberedWindowRawExchangeSymmetryTargets (HeadPairsSymmetric)
open NumberedWindowInternalLiteralAtomicLeastGuardProof (guardedLeast exact_LiteralAtomicGuardedLeast)
open NumberedWindowInternalLiteralHeaderLeastGuardProof (headerLeast exact_LiteralHeaderLeast)
open NumberedWindowInternalLiteralAuxProfileLeastProof (auxProfileLeast exact_LiteralAuxProfileLeast)
open NumberedWindowInternalLiteralFullAuxiliaryDecoratorProof (childGuardedLeast)
open NumberedWindowInternalLiteralAuxClassLeastProof
open NumberedWindowInternalLiteralClassGuardOnProof (classGuardWith)
open NumberedWindowInternalLiteralTypedMixedLeastProof (mixedFilteredLeast)

private theorem evalFunction (s : Settings) (K L : Program 3) (a : ActualLeastCalibration s K)
    (b : ActualLeastCalibration s L) (ctx q : Nat) :
    evaluate (functionClass K) (ctx ::ᵥ q ::ᵥ nil) =
      evaluate (functionClass L) (ctx ::ᵥ q ::ᵥ nil) := by
  unfold functionClass
  rw [compositeThree,compositeThree]
  rw [a,b]

private theorem evalArgument (s : Settings) (K L : Program 3) (a : ActualLeastCalibration s K)
    (b : ActualLeastCalibration s L) (ctx q : Nat) :
    evaluate (argumentClass K) (ctx ::ᵥ q ::ᵥ nil) =
      evaluate (argumentClass L) (ctx ::ᵥ q ::ᵥ nil) := by
  unfold argumentClass
  rw [compositeThree,compositeThree]
  rw [a,b]

private theorem compareCongr (P Q : Program 2)
    (agrees : ∀ c q, evaluate P (c ::ᵥ q ::ᵥ nil) = evaluate Q (c ::ᵥ q ::ᵥ nil))
    (xs : List.Vector Nat 3) :
    evaluate (compareChildClass P) xs = evaluate (compareChildClass Q) xs := by
  unfold compareChildClass
  rw [compositeTwo,compositeTwo]
  unfold onSource onResult
  rw [compositeTwo,compositeTwo,compositeTwo,compositeTwo]
  rw [agrees,agrees]

/-- Numerical agreement checks every input, including malformed inputs.
This theorem separately preserves the original semantics; it does not
transport any object derivation from one least program to the other. -/
theorem exact_LiteralClassGuardWithCalibration (s : Settings)
    (cover : WindowSeedsCovered s) (symmetry : HeadPairsSymmetric s.equivalentHeads)
    (K L : Program 3) (k : ActualLeastCalibration s K) (l : ActualLeastCalibration s L) :
    ActualLeastCalibration s (classGuardWith K L) := by
  intro ctx ty q
  have controls : ∀ xs, evaluate (checkAuxiliaryClasses K) xs =
      evaluate (checkAuxiliaryClasses L) xs := by
    intro xs
    unfold checkAuxiliaryClasses
    rw [evalBranch,evalBranch]
    split
    · rfl
    · unfold childClassesAgree
      rw [actualConjunctionEvaluation,actualConjunctionEvaluation,
        compareCongr _ _ (evalFunction s K L k l),compareCongr _ _ (evalArgument s K L k l)]
  have eq : evaluate (classGuardWith K L) (ctx ::ᵥ ty ::ᵥ q ::ᵥ nil) =
      evaluate (auxClassLeast L) (ctx ::ᵥ ty ::ᵥ q ::ᵥ nil) := by
    unfold classGuardWith auxClassLeast
    rw [compositeThree,compositeThree]
    unfold retainClasses
    rw [evalBranch,evalBranch,controls]
  rw [eq]
  exact exact_LiteralAuxClassLeast s cover symmetry L l ctx ty q

theorem exact_LiteralMixedFilteredCalibration (s : Settings)
    (cover : WindowSeedsCovered s) (symmetry : HeadPairsSymmetric s.equivalentHeads)
    (K L : Program 3) (k : ActualLeastCalibration s K) (l : ActualLeastCalibration s L) :
    ActualLeastCalibration s (mixedFilteredLeast K L) := by
  have child : ActualLeastCalibration s (childGuardedLeast L) :=
    exact_LiteralAtomicGuardedLeast s _ (exact_LiteralHeaderLeast s _ (exact_LiteralAuxProfileLeast s L l))
  have mid := exact_LiteralClassGuardWithCalibration s cover symmetry K (childGuardedLeast L) k child
  exact exact_LiteralAtomicGuardedLeast s _ (exact_LiteralHeaderLeast s _ mid)

#print axioms exact_LiteralClassGuardWithCalibration
#print axioms exact_LiteralMixedFilteredCalibration
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralTypedMixedCalibrationProof
