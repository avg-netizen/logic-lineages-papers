module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalApplicationCertificateConstructors
open InternalTagArithmeticSyntaxProof (eqn suc)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
def NativeOptional : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (U : Fin 19 → Program 3) (V : Program 3),
  (∀ i, i ≠ 14 → i ≠ 15 → ∀ v, evaluate (U i) v = fieldValue n arity i v) →
  (∀ v, evaluate V v = validValue n v) →
  ∀ v, evaluate (optional U V) v = ExchangeNumericSuppliers.layerValue n arity v
/-- Actual optional-layer factor, all output values, with actual runtime input
graphs. No supplier graph correctness is inferred from native calibration. -/
def InternalBodyFactor : Prop := ∀ (bodyFormula : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (U : Fin 19 → Program 3) (V : Program 3)
    (node code param out : OTerm alpha) (xs : Fin 19 → OTerm alpha),
  Nonempty (Derivation bodyFormula Delta (graph3 V (numeral 1) node code param)) →
  (∀ i, Nonempty (Derivation bodyFormula Delta (graph3 (fields U i) (xs i) node code param))) →
  (Nonempty (Derivation bodyFormula Delta (graph3 (optional U V) (suc out) node code param)) ↔
   Nonempty (Derivation bodyFormula Delta (programGraph ExchangeLayer.layer out xs)))
/-- Lambda constructor equation for this ACTUAL J AST: the recursive answer is
the real first list entry, not an assumed semantic law of an opaque J. -/
def InternalLambda : Prop := ∀ (bodyFormula : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (U : Fin 19 → Program 3) (V : Program 3)
    (node code param head tail : OTerm alpha) (xs : Fin 19 → OTerm alpha),
  Nonempty (Derivation bodyFormula Delta (graph3 V (numeral 1) node code param)) →
  (∀ i, Nonempty (Derivation bodyFormula Delta (graph3 (fields U i) (xs i) node code param))) →
  Nonempty (Derivation bodyFormula Delta (eqn (xs 0) (numeral 1))) →
  Nonempty (Derivation bodyFormula Delta (eqn (xs 7) (numeral 1))) →
  Nonempty (Derivation bodyFormula Delta (graph2 InternalListCodec.consCode code head tail)) →
  (Nonempty (Derivation bodyFormula Delta (graph3 (optional U V) (numeral 2) node code param)) ↔
   Nonempty (Derivation bodyFormula Delta (eqn (xs 1) (xs 8) ⊓ eqn head (numeral 1))))
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.TransparentExchangeLayer.Targets
