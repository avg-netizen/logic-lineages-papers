module

public import LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureMemoTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseRawFunctionFrameDefinitions

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (branch conjunction)
open InternalEqualityTest (subtract)
open InternalLessThan (ltTest)
open InternalRawListRecursion (lookup)
open NumberedWindowInternalSparsePathEnvelope (field)
open NumberedWindowInternalSparseRawFunctionFrame (termShape)
open NumberedWindowInternalAuxExchangeMemoStepTargets (binaryAfter unaryAfter currentKey)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)
open NumberedWindowInternalAuxMeasureMemoTargets (CombineCalibrated MeasureStepCalibrated selectedMeasure)

def shapeCheck : Program 4 := unaryAfter termShape currentKey

def childAt (i : Nat) : Program 4 := unaryAfter (field i) currentKey

def earlierAt (i : Nat) : Program 4 := binaryAfter ltTest (childAt i) currentKey

def offsetAt (i : Nat) : Program 4 := binaryAfter subtract (childAt i) (.projection 0)

def measureAt (i : Nat) : Program 4 := binaryAfter lookup (offsetAt i) (.projection 1)

def certain : Program 4 := conjunction shapeCheck (conjunction (earlierAt 2) (earlierAt 3))

def measureUpdate (base : Program 1) (P : Program 2) : Program 4 :=
  branch certain (unaryAfter base currentKey) (binaryAfter P (measureAt 2) (measureAt 3))

def ExactCombineProgram : Prop := ∃ P : Program 2, CombineCalibrated P

def ExactPhysicalAuxMeasureStep : Prop := ∀ (base : Program 1) (P : Program 2),
  CombineCalibrated P → MeasureStepCalibrated base (measureUpdate base P)

def ExactPhysicalAuxMeasure : Prop := ∀ (base : Program 1) (P : Program 2),
  TermMeasureCalibrated base → CombineCalibrated P → TermMeasureCalibrated (selectedMeasure (measureUpdate base P))

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureStepTargets
