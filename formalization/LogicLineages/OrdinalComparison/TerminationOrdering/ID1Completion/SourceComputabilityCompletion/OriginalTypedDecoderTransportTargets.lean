module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertion OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Forward acceptance by the ORIGINAL term checker under literal insertion
at any valid cutoff. The actual public shiftRaw graph supplies the transformed
raw term. The unchanged H, requested type and all original metadata remain
arbitrary; there is no native calibration or type-window premise. Rejection
is deliberately not transported on malformed raw syntax. -/
def ActualOriginalTypedInternalTermWeakening : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
    (d cutoff gamma extended typ raw shifted : OTerm alpha),
  Nonempty (Derivation body []
    ((Insert d cutoff gamma extended ⊓
      (graph2 shiftRaw shifted cutoff raw ⊓
        programGraph (OriginalTypedDecoder.termCheck H) (numeral 1) ![typ,raw,gamma])).imp
      (programGraph (OriginalTypedDecoder.termCheck H) (numeral 1) ![typ,shifted,extended])))

/-- The argument-list checker retains exactly the SAME requested type-list
code, not a decoded list or a newly selected checker. This includes every
original constructor and its literal recursive children. -/
def ActualOriginalTypedInternalArgumentsWeakening : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
    (d cutoff gamma extended types raw shifted : OTerm alpha),
  Nonempty (Derivation body []
    ((Insert d cutoff gamma extended ⊓
      (graph2 shiftRaw shifted cutoff raw ⊓
        programGraph (OriginalTypedDecoder.argumentsCheck H) (numeral 1) ![types,raw,gamma])).imp
      (programGraph (OriginalTypedDecoder.argumentsCheck H) (numeral 1) ![types,shifted,extended])))

/-- Guarded erasure starts from original acceptance in the extended context.
At the erased index this acceptance and literal insertion force requested
type = d. The actual eraseRaw graph then inserts bottom d. No erased-type
window, accepted-child-run or desired-transport premise is allowed. -/
def ActualOriginalTypedInternalTermErasure : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
    (d cutoff gamma extended typ raw erased : OTerm alpha),
  Nonempty (Derivation body []
    ((Insert d cutoff gamma extended ⊓
      (graph3 eraseRaw erased d cutoff raw ⊓
        programGraph (OriginalTypedDecoder.termCheck H) (numeral 1) ![typ,raw,extended])).imp
      (programGraph (OriginalTypedDecoder.termCheck H) (numeral 1) ![typ,erased,gamma])))

/-- Original arguments acceptance is preserved by guarded erasure at the
same arbitrary valid cutoff, with the requested type-list code unchanged.
The original checker runs at each raw input's own public raw+1 budget;
there is no numeric comparison of input and transformed raw codes. -/
def ActualOriginalTypedInternalArgumentsErasure : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (alpha : Type)
    (d cutoff gamma extended types raw erased : OTerm alpha),
  Nonempty (Derivation body []
    ((Insert d cutoff gamma extended ⊓
      (graph3 eraseRaw erased d cutoff raw ⊓
        programGraph (OriginalTypedDecoder.argumentsCheck H) (numeral 1) ![types,raw,extended])).imp
      (programGraph (OriginalTypedDecoder.argumentsCheck H) (numeral 1) ![types,erased,gamma])))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalTypedDecoderTransportTargets
