module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderInternalFuelDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuel
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalTypedDecoderStepSpecification
open OriginalTypedDecoderInternalFuel (WorkFuelGraph Terminal)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Actual original guarded Program 3, with unchanged separate outer context.
The internally generated live state uses the original raw worklist codec. -/
def WorkRun {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (out count workCode c : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (StepLive (.var (.inr (0 : Fin 1))) (workCode.relabel Sum.inl) ⊓
      graph3 (OriginalUniverseDecoder.iterate H M contextWindow) (out.relabel Sum.inl)
        (count.relabel Sum.inl) (.var (.inr (0 : Fin 1))) (c.relabel Sum.inl))

def SuccessfulWork {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode c : OTerm alpha) : Formula alpha :=
  WorkRun H M contextWindow (numeral 2) count workCode c

/-- Both the endpoint and its actual completed guarded execution are witnesses. -/
def TerminatedWork {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (count workCode c : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (WorkRun H M contextWindow (.var (.inr (0 : Fin 1))) (count.relabel Sum.inl)
        (workCode.relabel Sum.inl) (c.relabel Sum.inl) ⊓
      Terminal (.var (.inr (0 : Fin 1))))

/-- Precisely the existing typed raw+1 work weight. No new measure, changed
iterator, encoded context, window membership or successful-run premise. -/
def WorkAccepted {alpha : Type} (H : Program 1) (M contextWindow : Program 2)
    (workCode c : OTerm alpha) : Formula alpha :=
  InternalFiniteBlocks.block (k := 1)
    (WorkFuelGraph (.var (.inr (0 : Fin 1))) (workCode.relabel Sum.inl) ⊓
      SuccessfulWork H M contextWindow (.var (.inr (0 : Fin 1)))
        (workCode.relabel Sum.inl) (c.relabel Sum.inl))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderInternalFuel
