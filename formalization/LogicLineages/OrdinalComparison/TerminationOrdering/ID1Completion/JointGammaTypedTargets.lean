module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedTargets
open Source NumberedRewriteReduction NumberedLeastCodeRepresentative JointGammaTyped
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualRawTypedCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (symbols : List (Fin n)) (S Gamma : List Ty)
    (tau : Ty) (value : Nat),
  rawTypedCarrier n arity symbols S Gamma tau value =
    NumberedTypedCarrier.typedCanonicalCarrierTest n arity symbols S Gamma tau value

/-- Names the original checker directly, with Gamma inside the PR input. -/
def ActualOriginalTypedPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (fun p : Input n => NumberedTypedCarrier.typedCanonicalCarrierTest n arity
    p.1.1.1 p.1.1.2 p.1.2 p.2.1 p.2.2)

def ActualObjectTypedPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), Primrec (typedValue n arity)

def ActualOriginalContextFibers : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (Gamma : List Ty) (context typ value : Nat),
  (encodedTyped n arity context typ (ContextUniform.objectCode Gamma value) ↔
    OrdinaryArithmeticTypedCarrier.encodedTyped n arity Gamma context typ value)

/-- An actual finite Program and ordinary-arithmetic formula, calibrated on
all inputs and to the original well-typed source carrier. Not C_tau or ID1. -/
def ActualTypedArithmeticFormula : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ p : Program 3,
  (∀ v, evaluate p v = typedValue n arity v) ∧
  (∀ context typ object : Nat,
    (typedFormula p).Realize ![context,typ,object] ↔ encodedTyped n arity context typ object) ∧
  (∀ (symbols : List (Fin n)) (S : List Ty), SubtypeClosed (fun tau => tau ∈ S) →
    ∀ (table : Fin n → Fin n → Bool) (Gamma : List Ty) (tau : Ty) (value : Nat),
    (typedFormula p).Realize ![OrdinaryArithmeticQuotient.contextCode symbols S table,
      typeNumber tau,ContextUniform.objectCode Gamma value] ↔
    ∃ q : Packed (Fin n) arity Gamma, NumberedFiniteUniverse.InUniverse symbols S q.2 ∧
      q.1 = tau ∧ representativeCode symbols S q = value)

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.JointGammaTypedTargets
