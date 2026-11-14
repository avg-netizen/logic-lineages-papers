module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.Definitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.Targets
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalControlGraph
open InternalGraphComposition (OTerm)
open InternalControlGraphSupportProof (programGraph)
open InternalTagArithmeticSyntaxProof (eqn)
open SourceComputabilityFormulaSupportProof (numeral)
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram
/-- All original fields and arbitrary answer lists, including missing-answer defaults. -/
def NativeCalibration : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (p : NumberedExchangeCodePrimrecProof.LayerInput n),
  evaluate layer (input n arity p) = (NumberedExchangeCodePrimrecProof.layer n arity p).toNat
/-- The original recursive-call positions 0/3 and layer theorem are retained,
not asserted to be an internal self-recursive equation. -/
def NativeRecursiveLayer : Prop := ∀ (n : Nat) (arity : Fin n → Nat)
    (window : List (Fin n) × List Source.Ty) (source target : NumberedAuxiliaryCoding.Code (Fin n)),
  evaluate layer (input n arity (window,NumberedExchangeCodeFieldsProof.fields source,
    NumberedExchangeCodeFieldsProof.fields target,
    (NumberedExchangeCodeFieldsProof.dependencies (source,target)).map
      (fun p => NumberedExchangeCode.codeExchange arity window.1 window.2 p.1 p.2))) =
    (NumberedExchangeCode.codeExchange arity window.1 window.2 source target).toNat
/-- Actual internal lambda branch, with explicit actual tag equalities. -/
def InternalLambda : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (xs : Fin 19 → OTerm alpha),
  Nonempty (Derivation body Delta (eqn (xs 0) (numeral 1))) →
  Nonempty (Derivation body Delta (eqn (xs 7) (numeral 1))) →
  (Nonempty (Derivation body Delta (programGraph layer (numeral 1) xs)) ↔
   Nonempty (Derivation body Delta (eqn (xs 1) (xs 8) ⊓ eqn (xs 14) (numeral 1))))
/-- Both app and argumentsCons retain the literal sibling-equality disjunction. -/
def InternalApplication : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (xs : Fin 19 → OTerm alpha) (tag : Nat),
  (tag = 2 ∨ tag = 7) →
  Nonempty (Derivation body Delta (eqn (xs 0) (numeral tag))) →
  Nonempty (Derivation body Delta (eqn (xs 7) (numeral tag))) →
  (Nonempty (Derivation body Delta (programGraph layer (numeral 1) xs)) ↔
   Nonempty (Derivation body Delta (eqn (xs 1) (xs 8) ⊓
     ((eqn (xs 6) (xs 13) ⊓ eqn (xs 14) (numeral 1)) ⊔
      (eqn (xs 5) (xs 12) ⊓ eqn (xs 15) (numeral 1))))))
/-- Differing constructor tags internally reject, for arbitrary remaining slots. -/
def InternalTagMismatch : Prop := ∀ (body : Positive (Fin 1)) (alpha : Type)
    (Delta : List (Formula alpha)) (xs : Fin 19 → OTerm alpha),
  Nonempty (Derivation body Delta (eqn (xs 0) (xs 7)).not) →
  Nonempty (Derivation body Delta (programGraph layer (numeral 1) xs).not)
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.SourceComputabilityCompletion.Continuation20261114.ExchangeLayer.Targets
