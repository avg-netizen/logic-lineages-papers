module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectTransportDefinitions
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawVariableRankDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransport
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open OriginalRawObjectTransport OriginalRawVariableRank

/-- The original raw Object weakening preserves every variable occurrence.
The input and output may be arbitrary arithmetic codes; no typing, canonicality,
window, native evaluation or externally supplied pair coordinates are assumed. -/
def ShiftRankLaw : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (d input shifted rank : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph2 shiftObjectRaw shifted d input).imp
      ((graph1 variableRankObjectRaw rank shifted).iff
        (graph1 variableRankObjectRaw rank input))))

/-- The total raw Object eraser cannot increase the number of variable
occurrences, even for malformed codes or an empty decoded context. Its original
total destructors supply the domain and payload internally. This numeric rank
invariant does not assert contextual erasure transport, canonical cancellation
or any I/C law. -/
def EraseRankLaw : Prop :=
  ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (input erased before after : OTerm alpha),
  Nonempty (Derivation body Delta
    ((graph1 eraseObjectRaw erased input ⊓
      (graph1 variableRankObjectRaw before input ⊓
        graph1 variableRankObjectRaw after erased)).imp
      (RankNonincrease after before)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalRawObjectRankTransport
