module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalSelectionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutput
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open OriginalLambdaTraversalSelection
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The EXACT frozen four-part output invariant, including actual C-idempotence. -/
abbrev outputInvariant {alpha : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  OriginalLambdaTraversalSelection.OutputInvariant data window out input typ parameter

/-- Window, original source/type, and the actual C graph. The raw parameter
is universally quantified below, so each lambda IH can use its own childGamma. -/
def premises {alpha : Type} (data : Data) (window : Program 1)
    (out input typ parameter : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  OriginalFunctionNeutrality.windowGraph window input parameter ⊓
    (InternalParameterizedCanonicalResultFold.sourcePremises
      (leafData data window) input typ parameter ⊓
        InternalApplicationCertificateConstructors.graph2 (canonical data window) out input parameter)

/-- Input, raw type, actual output and parameter are ALL universally bound
inside the strong-payload invariant. The sole bound is the original right
payload, never parameter or the whole packed input. -/
def payloadMatrix {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 4) :=
  let input : OrdinaryArithmetic.Term (alpha ⊕ Fin 4) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (alpha ⊕ Fin 4) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 4) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (alpha ⊕ Fin 4) := .var (.inr 3)
  (InternalApplicationCertificateConstructors.graph1 InternalUnpair.right
    (payload.relabel Sum.inl) input).imp
      ((premises data window out input typ parameter).imp
        (outputInvariant data window out input typ parameter))

def atPayload {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (payloadMatrix data window payload)

def payloadPredicate (data : Data) (window : Program 1) {alpha : Type} :
    Formula (alpha ⊕ Fin 1) :=
  atPayload data window (.var (.inr 0))

def belowPayload {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalStrongInduction.below (payloadPredicate data window) payload

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutput
