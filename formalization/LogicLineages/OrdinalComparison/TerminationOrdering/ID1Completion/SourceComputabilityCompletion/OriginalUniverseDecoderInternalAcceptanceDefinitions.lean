module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuelDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalApplicationValidityStackAppendDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptance
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification OriginalUniverseDecoderInternalFuel
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- The unchanged original term checker, at its original raw+1 fuel. -/
def TermAccepted {alpha : Type} (H : Program 1) (M W : Program 2) (typ raw gamma c : OTerm alpha) : Formula alpha :=
  programGraph (OriginalUniverseDecoder.termCheck H M W) (numeral 1) ![typ,raw,gamma,c]

/-- The unchanged original arguments checker, at its original raw+1 fuel. -/
def ArgumentsAccepted {alpha : Type} (H : Program 1) (M W : Program 2) (types raw gamma c : OTerm alpha) : Formula alpha :=
  programGraph (OriginalUniverseDecoder.argumentsCheck H M W) (numeral 1) ![types,raw,gamma,c]

/-- The actual output state is live with internally witnessed accepted work.
Failure is excluded by the original pairing graph, not a replacement machine. -/
def AcceptedState {alpha : Type} (H : Program 1) (M W : Program 2) (state c : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (StepLive (state.relabel Sum.inl) (.var (.inr (0 : Fin 1))) ⊓
      WorkAccepted H M W (.var (.inr (0 : Fin 1))) (c.relabel Sum.inl))

/- Frozen acceptance support for the literal original guarded-source decoder. No native
calibration supplies arithmetic Derivations, and no typing/window/success
premise is introduced. All request fields, H, M, W and Gamma remain arbitrary. Every guard retains the SAME separate outer context c. -/
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalAcceptance
