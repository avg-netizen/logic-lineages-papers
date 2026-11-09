module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomParameterDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentative
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Compute the validator of the FINAL bottom-parameter/member-normalized
tuple before choosing the representative. V does not inspect oldR, so the
eventual source has definitionally this SAME validator. -/
def active (data : Data) (window : Program 1) : Program 2 :=
  BottomRepresentative.active (BottomParameter.baseData data) window

def sameMeasure (R : Program 2) : Program 2 :=
  InternalApplicationStepPeel.same
    (.composition BottomSpineMeasure.measure (fun _ : Fin 1 => R))
    (.composition BottomSpineMeasure.measure (fun _ : Fin 1 => .projection 0))

/-- On genuine source inputs primary equivalence already preserves the
FULL flag/depth mark. The literal comparison pays symbolic preservation;
all original inactive/malformed behavior is retained. -/
def representative (data : Data) (window : Program 1) : Program 2 :=
  InternalAcceptance.branch (active data window) data.oldRepresentative
    (InternalAcceptance.branch (sameMeasure data.oldRepresentative)
      (.projection 0) data.oldRepresentative)

/-- This globally selected tuple precedes BottomSource.selection. It does
not perform source/member normalization; the existing source pipeline does
each exactly once. Source, target and member leaves remain literal. -/
def baseData (data : Data) (window : Program 1) : Data :=
  { data with oldRepresentative := representative data window }

def activeGraph {α : Type} (data : Data) (window : Program 1)
    (value parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (active data window) InternalOriginalStepGuard.one value parameter

def representativeGraph {α : Type} (data : Data) (window : Program 1)
    (out value parameter : OrdinaryArithmetic.Term α) : Formula α :=
  graph2 (representative data window) out value parameter

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineRepresentative
