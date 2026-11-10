module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpineTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpine
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalApplicationSidecar
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Only the actual original observer graphs at one arbitrary encoded mark. -/
def conclusion {alpha : Type} (out input value : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  (BottomSpineMeasure.graph value out).iff (BottomSpineMeasure.graph value input)

/-- The unchanged full original antecedent, including its original window. -/
def premises {alpha : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises
      (originalData data window) input typ parameter ⊓
      InternalApplicationCertificateConstructors.graph2 (fold data window) out input parameter)

/-- All FIVE input/type/output/parameter/observer variables are universally
bound inside strong induction. Only the original right payload is bounded. -/
def payloadMatrix {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 5) :=
  let input : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 3)
  let value : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 4)
  (InternalApplicationCertificateConstructors.graph1 InternalUnpair.right
    (payload.relabel Sum.inl) input).imp
      ((premises data window out input typ parameter).imp (conclusion out input value))

def atPayload {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (payloadMatrix data window payload)

def payloadPredicate (data : Data) (window : Program 1) {alpha : Type} :
    Formula (alpha ⊕ Fin 1) :=
  atPayload data window (.var (.inr 0))

def belowPayload {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalStrongInduction.below (payloadPredicate data window) payload

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalApplicationSidecarSpine
