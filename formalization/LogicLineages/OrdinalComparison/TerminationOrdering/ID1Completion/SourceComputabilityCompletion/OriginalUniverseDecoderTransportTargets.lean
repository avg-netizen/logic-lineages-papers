module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalContextInsertionDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawSyntaxTransportDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open OriginalContextInsertion OriginalRawSyntaxTransport
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Forward acceptance by the ORIGINAL term checker under literal insertion
at any valid cutoff. The actual public shiftRaw graph supplies the transformed
raw term. The unchanged H, M, W, outer context c, requested type and all original metadata remain
arbitrary; there is no native calibration or type-window premise. Rejection
is deliberately not transported on malformed raw syntax. -/
def ActualOriginalUniverseInternalTermWeakening : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
    (d cutoff gamma extended typ raw shifted c : OTerm alpha),
  Nonempty (Derivation body []
    ((Insert d cutoff gamma extended ⊓
      (graph2 shiftRaw shifted cutoff raw ⊓
        programGraph (OriginalUniverseDecoder.termCheck H M W) (numeral 1) ![typ,raw,gamma,c])).imp
      (programGraph (OriginalUniverseDecoder.termCheck H M W) (numeral 1) ![typ,shifted,extended,c])))

/-- The argument-list checker retains exactly the SAME requested type-list
code, not a decoded list or a newly selected checker. This includes every
original constructor and its literal recursive children. -/
def ActualOriginalUniverseInternalArgumentsWeakening : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
    (d cutoff gamma extended types raw shifted c : OTerm alpha),
  Nonempty (Derivation body []
    ((Insert d cutoff gamma extended ⊓
      (graph2 shiftRaw shifted cutoff raw ⊓
        programGraph (OriginalUniverseDecoder.argumentsCheck H M W) (numeral 1) ![types,raw,gamma,c])).imp
      (programGraph (OriginalUniverseDecoder.argumentsCheck H M W) (numeral 1) ![types,shifted,extended,c])))

/-- Guarded erasure starts from original acceptance in the extended context.
At the erased index this acceptance and literal insertion force requested
type = d. Its SAME source acceptance supplies M(requested type,c), and the actual eraseRaw graph then inserts bottom d. No erased-type
window, accepted-child-run or desired-transport premise is allowed. -/
def ActualOriginalUniverseInternalTermErasure : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
    (d cutoff gamma extended typ raw erased c : OTerm alpha),
  Nonempty (Derivation body []
    ((Insert d cutoff gamma extended ⊓
      (graph3 eraseRaw erased d cutoff raw ⊓
        programGraph (OriginalUniverseDecoder.termCheck H M W) (numeral 1) ![typ,raw,extended,c])).imp
      (programGraph (OriginalUniverseDecoder.termCheck H M W) (numeral 1) ![typ,erased,gamma,c])))

/-- Original arguments acceptance is preserved by guarded erasure at the
same arbitrary valid cutoff, with the requested type-list code unchanged.
The original checker runs at each raw input's own public raw+1 budget;
there is no numeric comparison of input and transformed raw codes. -/
def ActualOriginalUniverseInternalArgumentsErasure : Prop :=
  ∀ (body : Positive (Fin 1)) (H : Program 1) (M W : Program 2) (alpha : Type)
    (d cutoff gamma extended types raw erased c : OTerm alpha),
  Nonempty (Derivation body []
    ((Insert d cutoff gamma extended ⊓
      (graph3 eraseRaw erased d cutoff raw ⊓
        programGraph (OriginalUniverseDecoder.argumentsCheck H M W) (numeral 1) ![types,raw,extended,c])).imp
      (programGraph (OriginalUniverseDecoder.argumentsCheck H M W) (numeral 1) ![types,erased,gamma,c])))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalUniverseDecoderTransportTargets
