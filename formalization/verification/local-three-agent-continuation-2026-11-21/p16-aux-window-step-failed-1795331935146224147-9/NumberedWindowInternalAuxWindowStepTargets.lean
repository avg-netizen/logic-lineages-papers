module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowMemoTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparsePairTargets

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction)
open InternalEqualityTest (equalityTest)
open NumberedWindowInternalSparsePathEnvelope (run)
open NumberedWindowInternalSparsePair (fieldCons)
open NumberedWindowInternalAuxExchangeMemoStepTargets (unaryAfter binaryAfter currentKey)
open NumberedWindowInternalAuxMeasureStepTargets (certain childAt measureAt)
open NumberedWindowInternalAuxWindowMemoTargets
open NumberedWindowInternalSparseTypedRawTargets (ActualPackedWindow)
open NumberedWindowScalarAlgorithm (Settings)

def TypeGuardCalibrated (s : Settings) (T : Program 1) : Prop :=
  ∀ ty, run T ty = (typeGuard s ty).toNat

def resultCode : Program 4 := unaryAfter .succ (childAt 1)
def argumentCode : Program 4 := unaryAfter .succ (childAt 0)
def functionCode : Program 4 := unaryAfter .succ (binaryAfter fieldCons (childAt 0) (childAt 1))

def reportTest (slot : Nat) (code : Program 4) : Program 4 :=
  binaryAfter equalityTest (measureAt slot) code

def admittedChildren (T : Program 1) : Program 4 :=
  conjunction (unaryAfter T (childAt 0))
    (conjunction (unaryAfter T (childAt 1))
      (conjunction (reportTest 2 functionCode) (reportTest 3 argumentCode)))

def windowUpdate (base : Program 2) (T : Program 1) : Program 4 :=
  branch (conjunction certain (admittedChildren T))
    (binaryAfter base (.projection 2) currentKey) resultCode

def intrinsicQuery (F : Program 2) : Program 3 :=
  .composition equalityTest
    ![.composition F ![.projection 0,.projection 2], .composition .succ ![.projection 1]]

def ExactWindowPrimitiveLeaves : Prop := ∀ (s : Settings),
  ∃ (base : Program 2) (T : Program 1), IntrinsicWindowCalibrated s base ∧ TypeGuardCalibrated s T

def ExactPhysicalAuxWindowStep : Prop := ∀ (s : Settings) (base : Program 2) (T : Program 1),
  TypeGuardCalibrated s T → WindowStepCalibrated s base (windowUpdate base T)

def ExactPhysicalAuxWindow : Prop := ∀ (s : Settings) (base : Program 2) (T : Program 1),
  IntrinsicWindowCalibrated s base → TypeGuardCalibrated s T →
  ActualPackedWindow s (intrinsicQuery (selectedIntrinsic (windowUpdate base T)))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxWindowStepTargets
