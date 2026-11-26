module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261112.Context.DeletionMapTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.OriginalReverseConsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ListGeometryTargets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- Unary original map commutes with actual encoded append. -/
def UnaryMapAppend : Prop := ∀ (F : Program 1)
    (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right joined mappedLeft mappedRight out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined left right)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) mappedLeft left)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) mappedRight right)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out mappedLeft mappedRight)) →
  Nonempty (Derivation body Delta (graph1 (InternalListMap.map (k := 0) F) out joined))
/-- Reversal switches append order on the unchanged internal numeric codec. -/
def ReverseAppend : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type) (Delta : List (Formula alpha))
    (left right joined reverseLeft reverseRight out : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append joined left right)) →
  Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reverseLeft left)) →
  Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse reverseRight right)) →
  Nonempty (Derivation body Delta (graph2 InternalApplicationValidityStackAppend.append out reverseRight reverseLeft)) →
  Nonempty (Derivation body Delta (graph1 OriginalTypedArgumentObservations.reverse out joined))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.SixSol20261113.Context.ListGeometryTargets
