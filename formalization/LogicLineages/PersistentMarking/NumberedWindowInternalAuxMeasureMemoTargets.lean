module

public import LogicLineages.PersistentMarking.NumberedWindowInternalFactoredCoverTargets
public import LogicLineages.PersistentMarking.NumberedWindowInternalSparseFieldParser

@[expose] public section
namespace LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureMemoTargets
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram List.Vector
open LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion
open InternalAcceptance (constantZero)
open InternalRawListRecursion (lookup)
open NumberedWindowCoverBoundsAlgorithm (Measure bounds)
open NumberedWindowFieldAlgorithm (unpackNode)
open NumberedWindowInternalSparseFieldParser (scratchRow)
open NumberedWindowInternalFactoredCoverTargets (TermMeasureCalibrated)

/-- The two original measure coordinates at a literal auxiliary application. -/
def auxiliaryMeasure (fn arg : Measure) : Measure :=
  (fn.1 + arg.1 + 1, max fn.2 arg.2)

def readMeasure (n : Nat) : Measure := ((Encodable.decode n : Option Measure).getD (0,0))

def combine (fn arg : Nat) : Nat := Encodable.encode (auxiliaryMeasure (readMeasure fn) (readMeasure arg))

def CombineCalibrated (P : Program 2) : Prop := ∀ fn arg,
  evaluate P (fn ::ᵥ arg ::ᵥ nil) = combine fn arg

/-- The step uses the same earlier physical table at both actual child keys.
Every other case has the retained original term measure as its fallback. -/
def measureStepValue (base : Program 1) (i old : Nat) : Nat :=
  let original := evaluate base ((i+1) ::ᵥ nil)
  match unpackNode (i+1) with
  | some (6,[_,_,fn,arg]) =>
    if fn < i+1 ∧ arg < i+1 then
      combine (evaluate lookup ((i-fn) ::ᵥ old ::ᵥ nil))
        (evaluate lookup ((i-arg) ::ᵥ old ::ᵥ nil))
    else original
  | _ => original

def MeasureStepCalibrated (base : Program 1) (R : Program 4) : Prop :=
  ∀ i old, evaluate R (i ::ᵥ old ::ᵥ 0 ::ᵥ 0 ::ᵥ nil) = measureStepValue base i old

def selectedMeasure (R : Program 4) : Program 1 :=
  .composition (scratchRow (constantZero 2) R)
    (Fin.cons (.projection 0) (Fin.cons (constantZero 1) (Fin.cons (constantZero 1) Fin.elim0)))

def ExactAuxMeasureRecurrence : Prop := ∀ raw dom cod fn arg,
  unpackNode raw = some (6,[dom,cod,fn,arg]) →
  (bounds raw).1 = auxiliaryMeasure (bounds fn).1 (bounds arg).1

def ExactAuxMeasureCalibration : Prop := ∀ (base : Program 1) (R : Program 4),
  TermMeasureCalibrated base → MeasureStepCalibrated base R → TermMeasureCalibrated (selectedMeasure R)

end LogicLineages.PersistentMarking.NumberedWindowInternalAuxMeasureMemoTargets
