module

public import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoLeastProof
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowOpenTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePassWindowTargets
import LogicLineages.PersistentMarking.NumberedWindowInternalLiteralCoveredMemoNumericProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseCoverScratchNumericProjectionProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePackedLeastNumericTapeProof
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseScratchMembershipNumericChecks
import LogicLineages.PersistentMarking.NumberedWindowInternalSparseOrderedMinimumNumericStepProof
import LogicLineages.PersistentMarking.NumberedWindowInternalFreshProbeDispatchProgramControlProof
import LogicLineages.OrdinalComparison.TerminationOrdering.NumberedMultisetNumericSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalEqualityTestEvaluationProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceSupportProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceConjunctionProof
import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalAcceptanceCalibrationProof

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationCoverageWindowProof
open FirstOrder Language LogicLineages.OrdinalComparison.TerminationOrdering
open PositiveArithmeticOperators ID1Completion.InternalCalculus ID1Completion.InternalControlGraph
open ID1Completion.InternalGraphComposition (OTerm)
open ID1Completion.InternalControlGraphSupportProof (compositionValue projectionValue)
open ID1Completion.InternalAcceptance (branch conjunction constantZero)
open ID1Completion.InternalAcceptanceSupportProof (compositionRecover)
open ID1Completion.InternalAcceptanceConjunctionProof (constantZeroValue conjunctionAccept conjunctionRecover)
open ID1Completion.InternalAcceptanceCalibrationProof (actualConjunctionEvaluation evalBranch)
open ID1Completion.InternalEqualityTestEvaluationProof (vectorTwo)
open LogicLineages.ComputabilityKnowledge GorbowPRProgram List.Vector
open NumberedWindowScalarAlgorithm (Settings admitted vertices)
open NumberedWindowFieldAlgorithm (unpack)
open NumberedMultisetNumeric (numbersNumber)
open NumberedMultisetNumericSupportProof (numbersRoundTrip)
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow packedWindow)
open NumberedWindowInternalSparseCoverScratchTargets (ActualSelectedCoverOutput)
open NumberedWindowInternalSparsePackedLeast (contextOption poolAtSeed)
open NumberedWindowInternalSparseCoverScratchNumericProjectionProof (scratchVerticesValue)
open NumberedWindowInternalSparsePackedLeastNumericTapeProof (contextValue)
open NumberedWindowInternalSparseOrderedMinimumNumericStepProof (unaryValue)
open NumberedWindowInternalSparseScratchMembership (scratchMember)
open NumberedWindowInternalSparseScratchMembershipNumericChecks (exact_AllInputScratchMembership)
open NumberedWindowInternalLiteralCoveredMemo (contextPresent ownSeed WindowSeedsCovered)
open NumberedWindowInternalLiteralCoveredMemoRowSupportProof (coverageReport)
open NumberedWindowInternalFreshProbeDispatchProgramControlProof (compositeThree)
open NumberedWindowInternalAuxWindowStepTargets (windowUpdate intrinsicQuery)
open NumberedWindowInternalAuxWindowMemoTargets (selectedIntrinsic)
open NumberedWindowInternalSparsePathEnvelopeTargets (z suc)
open NumberedWindowInternalSparsePassWindowTargets (windowAt)

attribute [local irreducible] programGraph
abbrev D (B : Positive (Fin 1)) {α : Type} (Γ : List (Formula α)) (f : Formula α) :=
  Nonempty (Derivation B Γ f)
variable {B : Positive (Fin 1)} {α : Type} {Γ : List (Formula α)}

def simpleFormationWindow (base : Program 2) (T : Program 1) : Program 3 :=
  intrinsicQuery (selectedIntrinsic (windowUpdate base T))

def directCoverage (C : Program 3) (s : Settings) : Program 3 :=
  .composition (conjunction contextPresent (ownSeed C s))
    (Fin.cons (.projection 0) (Fin.cons (constantZero 3) (Fin.cons (.projection 2) Fin.elim0)))

/-- Use the genuine recursively forming window, with a separate
literal cover/context check on the very same seed. Thus both its
formation rule and its least domain can be used internally. -/
def coveredFormationWindow (C : Program 3) (s : Settings) (base : Program 2) (T : Program 1) : Program 3 :=
  conjunction (simpleFormationWindow base T) (directCoverage C s)

private theorem ownValue (C : Program 3) (s : Settings) (hC : ActualSelectedCoverOutput C)
    (ctx seed : Nat) : evaluate (ownSeed C s) (ctx ::ᵥ 0 ::ᵥ seed ::ᵥ nil) =
      ((vertices s seed).any (fun h => h == seed)).toNat := by
  let xs := ctx ::ᵥ 0 ::ᵥ seed ::ᵥ nil
  have v : evaluate (poolAtSeed C s) xs = numbersNumber (vertices s seed) := by
    rw [poolAtSeed,unaryValue]
    exact scratchVerticesValue C hC s seed
  change evaluate scratchMember (List.Vector.ofFn (fun i : Fin 2 =>
    evaluate ((![poolAtSeed C s,.projection 2] : Fin 2 → Program 3) i) xs)) = _
  rw [vectorTwo]
  change evaluate scratchMember (evaluate (poolAtSeed C s) xs ::ᵥ seed ::ᵥ nil) = _
  rw [v,exact_AllInputScratchMembership,numbersRoundTrip]
  rfl

theorem exact_CoveredFormationWindowCalibration (C : Program 3) (s : Settings) (base : Program 2)
    (T : Program 1) (cover : ActualSelectedCoverOutput C) (seeds : WindowSeedsCovered s)
    (old : ActualPackedWindow s (simpleFormationWindow base T)) :
    ActualPackedWindow s (coveredFormationWindow C s base T) := by
  intro ctx ty seed
  rw [coveredFormationWindow,actualConjunctionEvaluation,old ctx ty seed]
  cases ok : packedWindow s ctx ty seed with
  | false => simp
  | true =>
    obtain ⟨g,hc,admittedHere⟩ : ∃ g, unpack ctx = some g ∧ admitted s g ty seed = true := by
      cases h : unpack ctx with
      | none => simp [packedWindow,h] at ok
      | some g => exact ⟨g,rfl,by simpa [packedWindow,h] using ok⟩
    have ctxOK : evaluate contextPresent (ctx ::ᵥ 0 ::ᵥ seed ::ᵥ nil) = 1 := by
      rw [contextPresent,evalBranch,contextValue,hc]
      rfl
    have hit : evaluate (ownSeed C s) (ctx ::ᵥ 0 ::ᵥ seed ::ᵥ nil) = 1 := by
      rw [ownValue C s cover ctx seed]
      simp [seeds g ty seed admittedHere]
    have coverage : evaluate (directCoverage C s) (ctx ::ᵥ ty ::ᵥ seed ::ᵥ nil) = 1 := by
      rw [directCoverage,compositeThree]
      change evaluate (conjunction contextPresent (ownSeed C s)) (ctx ::ᵥ 0 ::ᵥ seed ::ᵥ nil) = 1
      rw [actualConjunctionEvaluation,ctxOK,hit]
      rfl
    simp [coverage]

/-- Both selected programs can be opened on a successful window;
conversely their actual reports construct the same new window. -/
theorem exact_OpenCoveredFormationWindow (C : Program 3) (s : Settings) (base : Program 2)
    (T : Program 1) (ctx ty q : OTerm α) :
    (D B Γ (windowAt (coveredFormationWindow C s base T) ctx ty q) →
      D B Γ (windowAt (simpleFormationWindow base T) ctx ty q) ∧ D B Γ (coverageReport C s ctx q)) ∧
    (D B Γ (windowAt (simpleFormationWindow base T) ctx ty q) →
      D B Γ (coverageReport C s ctx q) → D B Γ (windowAt (coveredFormationWindow C s base T) ctx ty q)) := by
  let xs : Fin 3 → OTerm α := ![ctx,ty,q]
  let fs : Fin 3 → Program 3 :=
    Fin.cons (.projection 0) (Fin.cons (constantZero 3) (Fin.cons (.projection 2) Fin.elim0))
  have inputs (i : Fin 3) : D B Γ (programGraph (fs i) ((![ctx,z,q] : Fin 3 → OTerm α) i) xs) :=
    Fin.cases (projectionValue 0 xs) (Fin.cases (constantZeroValue xs)
      (Fin.cases (projectionValue 2 xs) (fun e => Fin.elim0 e))) i
  constructor
  · intro h
    obtain ⟨pair⟩ := conjunctionRecover (simpleFormationWindow base T) (directCoverage C s) xs h
    exact ⟨⟨Derivation.conjunctionLeft pair⟩,compositionRecover
      (conjunction contextPresent (ownSeed C s)) fs (suc z) xs ![ctx,z,q]
      ⟨Derivation.conjunctionRight pair⟩ inputs⟩
  · intro h cover
    have check := compositionValue (conjunction contextPresent (ownSeed C s)) fs (suc z) xs
      ![ctx,z,q] cover inputs
    exact conjunctionAccept (simpleFormationWindow base T) (directCoverage C s) xs h check

#print axioms exact_CoveredFormationWindowCalibration
#print axioms exact_OpenCoveredFormationWindow
end LogicLineages.PersistentMarking.NumberedWindowInternalLiteralApplicationCoverageWindowProof
