module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalLambdaTraversalOutputDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankObserverProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalApplicationCertificateConstructors
open InternalOriginalUniformDescentSelection (Data)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The actual all-variable-occurrence observer, independent of native calibration. -/
def observations {alpha : Type} (out input mark : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw mark out).iff
    (graph1 OriginalRawSyntaxTransport.variableRankPackedRaw mark input)

abbrev premises := @OriginalLambdaTraversalOutput.premises

/-- The mark, input, type, output and runtime parameter all remain internally
universal. Lambda visits may therefore use their own actual child Gamma. -/
def payloadMatrix {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 5) :=
  let input : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 3)
  let mark : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 4)
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) input).imp
    ((premises data window out input typ parameter).imp (observations out input mark))

def atPayload {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (payloadMatrix data window payload)

def payloadPredicate (data : Data) (window : Program 1) {alpha : Type} : Formula (alpha ⊕ Fin 1) :=
  atPayload data window (.var (.inr 0))

def belowPayload {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalStrongInduction.below (payloadPredicate data window) payload

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFinalGuardedRankObserverProof
