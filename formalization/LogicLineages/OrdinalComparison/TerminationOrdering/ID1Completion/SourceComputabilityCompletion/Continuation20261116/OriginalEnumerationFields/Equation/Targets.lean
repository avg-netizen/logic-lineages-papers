module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.Targets
open Continuation20261115
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open Continuation20261114
/-- The actual previous own-root table, at its actual projected-raw rank stage (not successor rank), agrees with
the standalone ordered child map. Nonmissingness, alignment and extraction are
internal duties. No native image, valid-code or child agreement premise. -/
def InternalPreviousAnswers : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (raw param nodeRank old deps values : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.rank nodeRank raw param)) →
  Nonempty (Derivation body Delta (graph3 (OriginalEnumerationFields.graph n) old nodeRank raw param)) →
  Nonempty (Derivation body Delta (graph2 OriginalEnumerationFields.dependency deps raw param)) →
  (Nonempty (Derivation body Delta (graph2 (answerMap n) values deps param)) ↔
   Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph values deps old)))
/-- Actual keyed Fields recurrence: extraction is a Fields payload, whereas
layer output is Some(payload). In particular invalid totalized Fields payload0
has layer output1. The entire ordered answer list is produced by the concrete
AST, with no additional validity or recursive-value assumptions. -/
def InternalFieldsEquation : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha)) (raw param values value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (answers n) values raw param)) →
  (Nonempty (Derivation body Delta (graph2 (OriginalEnumerationFields.extract n) value raw param)) ↔
   Nonempty (Derivation body Delta (graph3 (OriginalEnumerationFields.layer n) (suc value) raw values param)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261116.OriginalEnumerationFields.Equation.Targets
