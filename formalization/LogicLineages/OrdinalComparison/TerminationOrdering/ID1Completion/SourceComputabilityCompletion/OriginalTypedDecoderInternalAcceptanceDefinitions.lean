module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptance
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalTypedDecoderInternalFuel
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The unchanged original term checker, at its original raw+1 fuel. -/
def TermAccepted {alpha : Type} (H : Program 1) (typ raw gamma : OTerm alpha) : Formula alpha :=
  programGraph (OriginalTypedDecoder.termCheck H) (numeral 1) ![typ,raw,gamma]

/-- The unchanged original arguments checker, at its original raw+1 fuel. -/
def ArgumentsAccepted {alpha : Type} (H : Program 1) (types raw gamma : OTerm alpha) : Formula alpha :=
  programGraph (OriginalTypedDecoder.argumentsCheck H) (numeral 1) ![types,raw,gamma]

/-- The actual output state is live with internally witnessed accepted work.
Failure is excluded by the original pairing graph, not a replacement machine. -/
def AcceptedState {alpha : Type} (H : Program 1) (state : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (StepLive (state.relabel Sum.inl) (.var (.inr (0 : Fin 1))) ⊓
      WorkAccepted H (.var (.inr (0 : Fin 1))))

/- Frozen acceptance support for the literal original typed decoder. No native
calibration supplies arithmetic Derivations, and no typing/window/success
premise is introduced. All request fields, H and Gamma remain arbitrary. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalAcceptance
