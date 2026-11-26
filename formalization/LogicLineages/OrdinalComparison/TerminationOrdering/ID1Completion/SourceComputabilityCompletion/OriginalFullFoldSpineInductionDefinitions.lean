module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpineDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpine
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalOriginalUniformDescentSelection (Data)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Input, type, output, parameter and the WHOLE observer mark are bound
inside the induction predicate. Only the original right payload is bounded. -/
def payloadMatrix {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula (alpha ⊕ Fin 5) :=
  let input : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 0)
  let typ : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 1)
  let out : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 2)
  let parameter : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 3)
  let mark : OrdinaryArithmetic.Term (alpha ⊕ Fin 5) := .var (.inr 4)
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) input).imp
    ((premises data window out input typ parameter).imp (conclusion out input mark))

def atPayload {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (payloadMatrix data window payload)

def payloadPredicate (data : Data) (window : Program 1) {alpha : Type} :
    Formula (alpha ⊕ Fin 1) :=
  atPayload data window (.var (.inr 0))

def belowPayload {alpha : Type} (data : Data) (window : Program 1)
    (payload : OrdinaryArithmetic.Term alpha) : Formula alpha :=
  InternalStrongInduction.below (payloadPredicate data window) payload

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalFullFoldSpine
