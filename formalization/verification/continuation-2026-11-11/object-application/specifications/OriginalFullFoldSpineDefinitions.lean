module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.BottomSpineMeasureDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SpineApplicationTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpine
open FirstOrder Language PositiveArithmeticOperators InternalCalculus
open InternalGraphComposition (OTerm)
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Preserve the WHOLE original bottom-spine observer value, including its
flag and depth, at every symbolic mark. This is not a Boolean-only law. -/
def conclusion {alpha : Type} (out input mark : OTerm alpha) : Formula alpha :=
  (BottomSpineMeasure.graph mark out).iff (BottomSpineMeasure.graph mark input)

/-- The original active window, actual source validity/type and SAME full
canonical fold. No child witness, representative equation or fixedness
assumption is supplied by the caller. -/
def premises {alpha : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OTerm alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises data input typ parameter ⊓
      InternalParameterizedCanonicalResultFold.foldGraph data out input parameter)

/-- Closed internal full-N mark preservation at one literal Data/window
tuple. Input, output, type, parameter, mark and source context remain arbitrary. -/
def FullFoldMarkPreservation (data : Data) (window : Program 1) : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Gamma : List (Formula alpha))
    (out input typ parameter mark : OTerm alpha),
  Nonempty (Derivation body Gamma
    ((premises data window out input typ parameter).imp (conclusion out input mark)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpine
