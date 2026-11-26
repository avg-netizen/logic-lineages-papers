module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalClosedProgramsDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalStrongInductionDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInduction
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Pointwise acceptance equality of two actual binary Programs. -/
def Acceptance {alpha : Type} (left right : Program 2)
    (raw parameter : OTerm alpha) : Formula alpha :=
  (graph2 left (numeral 1) raw parameter).iff
    (graph2 right (numeral 1) raw parameter)

/-- Every original packed raw value and runtime parameter is universally
bound inside the induction predicate, with only its actual payload fixed. -/
def payloadMatrix {alpha : Type} (left right : Program 2)
    (payload : OTerm alpha) : Formula (alpha ⊕ Fin 2) :=
  let raw : OTerm (alpha ⊕ Fin 2) := .var (.inr 0)
  let parameter : OTerm (alpha ⊕ Fin 2) := .var (.inr 1)
  (graph1 InternalUnpair.right (payload.relabel Sum.inl) raw).imp
    (Acceptance left right raw parameter)

def atPayload {alpha : Type} (left right : Program 2)
    (payload : OTerm alpha) : Formula alpha :=
  InternalClosedPrograms.allBlock (payloadMatrix left right payload)

def payloadPredicate (left right : Program 2) {alpha : Type} : Formula (alpha ⊕ Fin 1) :=
  atPayload left right (.var (.inr 0))

def belowPayload {alpha : Type} (left right : Program 2)
    (payload : OTerm alpha) : Formula alpha :=
  InternalStrongInduction.below (payloadPredicate left right) payload

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTransparentDecoderValidatorCollapseInduction
