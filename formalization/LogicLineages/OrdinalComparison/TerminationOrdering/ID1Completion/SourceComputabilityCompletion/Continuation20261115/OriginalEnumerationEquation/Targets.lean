module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (suc)
open Continuation20261114
/-- The actual previous own-root table at OBSERVED R(node), not raw node and
not successor rank, yields exactly the ordered standalone child answers.
Coverage, rank-zero emptiness, Some-definedness and extraction are internal. -/
def InternalPreviousAnswers : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (node param rank old deps values : OTerm alpha),
  Nonempty (Derivation body Delta
    (graph2 OriginalEnumerationRecursionInterface.R rank node param)) →
  Nonempty (Derivation body Delta
    (graph3 (OriginalEnumerationRecursion.graph n) old rank node param)) →
  Nonempty (Derivation body Delta
    (graph2 OriginalEnumerationRecursionInterface.D deps node param)) →
  (Nonempty (Derivation body Delta (graph2 (answerMap n) values deps param)) ↔
   Nonempty (Derivation body Delta (graph2 ExchangeMapGraph.mapGraph values deps old)))
/-- All-raw literal standalone recurrence. Enumeration returns the payload;
G returns Some(payload), including Some(empty-list code0)=1. Actual ordered
answers are observed, not supplied recursive-value or agreement assumptions. -/
def InternalEnumerationEquation : Prop := ∀ (n : Nat) (body : Positive (Fin 1))
    (alpha : Type) (Delta : List (Formula alpha))
    (node param values value : OTerm alpha),
  Nonempty (Derivation body Delta (graph2 (answers n) values node param)) →
  (Nonempty (Derivation body Delta
    (graph2 (OriginalEnumerationRecursion.enumeration n) value node param)) ↔
   Nonempty (Derivation body Delta
    (graph3 (OriginalEnumerationRecursionInterface.G n) (suc value) node values param)))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261115.OriginalEnumerationEquation.Targets
