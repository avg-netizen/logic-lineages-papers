module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierTargets
open FirstOrder Language Source PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalControlGraph
open InternalOriginalTypedCarrier
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

/-- Select one actual old typed Program for each fixed original signature,
arbitrary finite window and Gamma, before all natural value/type inputs. -/
def ActualOriginalTypedProgramExists : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty),
  ∃ oldTyped : Program 2, Calibrated n arity symbols S Gamma oldTyped

/-- The explicit guarded wrapper preserves the ENTIRE original zero/one
function. Its proof must establish that original canonical-typed acceptance
already implies source-universe validity and equality of the raw outer tag
to the supplied code. No valid-input, successful-decoding or subtype-closure
premise is introduced, and the original representative condition is retained. -/
def ActualOriginalTypedWrapperCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (validity : InternalOriginalStepGuard.Data) (oldTyped : Program 2),
  InternalOriginalStepGuard.Calibrated n arity symbols S Gamma validity →
  Calibrated n arity symbols S Gamma oldTyped →
  Calibrated n arity symbols S Gamma (checker validity oldTyped)

/-- Actual internal factorization and introduction for the concrete AST.
Acceptance derives BOTH original source validity and the raw outer-tag graph,
with no supplied tag witness, external calibration or truth-to-proof premise.
This holds for arbitrary Program leaves, body and symbolic value/type terms. -/
def ActualOriginalTypedAcceptanceEquation : Prop :=
  ∀ (body : Positive (Fin 1)) (validity : InternalOriginalStepGuard.Data) (oldTyped : Program 2)
    (α : Type) (value typ : OTerm α),
  Nonempty (Derivation body []
    ((accepted validity oldTyped value typ).iff
      (requirements validity oldTyped value typ)))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalOriginalTypedCarrierTargets
