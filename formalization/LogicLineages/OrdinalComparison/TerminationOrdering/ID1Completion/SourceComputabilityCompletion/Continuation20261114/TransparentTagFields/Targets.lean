module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All numeric vectors, including every malformed node and window branch. -/
def NativeTags : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (V : Program 3),
  (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) →
  ∀ v, evaluate (sourceTag V) v = TransparentExchangeLayer.fieldValue n arity 0 v ∧
    evaluate (targetTag V) v = TransparentExchangeLayer.fieldValue n arity 7 v
/-- Actual nested pair graphs, not native decoder reflection. This supplies
both constructor tags for the same guarded ASTs on symbolic arithmetic inputs. -/
def InternalTags : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3)
    (node code param source target sourceTagValue sourcePayload targetTagValue targetPayload : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing node source target)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing source sourceTagValue sourcePayload)) →
  Nonempty (Derivation body Delta (graph2 InternalPairing.pairing target targetTagValue targetPayload)) →
  Nonempty (Derivation body Delta (graph3 (sourceTag V) sourceTagValue node code param)) ∧
  Nonempty (Derivation body Delta (graph3 (targetTag V) targetTagValue node code param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentTagFields.Targets
