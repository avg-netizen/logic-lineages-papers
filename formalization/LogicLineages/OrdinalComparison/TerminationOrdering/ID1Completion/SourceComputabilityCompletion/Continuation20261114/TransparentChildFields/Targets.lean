module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeChildren : Prop := ∀ (n : Nat) (arity : Fin n → Nat) (V : Program 3),
  (∀ v, evaluate V v = TransparentExchangeLayer.validValue n v) →
  ∀ (target : Bool) v,
    evaluate (first V target) v = TransparentExchangeLayer.fieldValue n arity (if target then 12 else 5) v ∧
    evaluate (second V target) v = TransparentExchangeLayer.fieldValue n arity (if target then 13 else 6) v
/-- Symbolic original lambda-constructor graph, for either actual node side. -/
def InternalLambda : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3) (target : Bool)
    (node code param raw domain child : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph3 (rawCode target) raw node code param)) →
  Nonempty (Derivation body Delta (graph2 OriginalRawSyntaxTransport.lambdaConstructor raw domain child)) →
  Nonempty (Derivation body Delta (graph3 (first V target) child node code param)) ∧
  Nonempty (Derivation body Delta (graph3 (second V target) (numeral 0) node code param))
/-- Original app/argsCons graph, not an assumed selector correctness law. -/
def InternalApplication : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (V : Program 3) (target cons : Bool)
    (node code param raw domain left right : OTerm alpha),
  Nonempty (Derivation body Delta (graph3 V (numeral 1) node code param)) →
  Nonempty (Derivation body Delta (graph3 (rawCode target) raw node code param)) →
  Nonempty (Derivation body Delta
    (graph3 (if cons then OriginalRawSyntaxTransport.consConstructor else OriginalRawSyntaxTransport.applicationConstructor)
      raw domain left right)) →
  Nonempty (Derivation body Delta (graph3 (first V target) left node code param)) ∧
  Nonempty (Derivation body Delta (graph3 (second V target) right node code param))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentChildFields.Targets
