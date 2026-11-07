module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainTargets
open Source ApplicationDomain ApplicationResultBuilder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualArrowCalibration : Prop :=
  ∀ domain codomain : Nat, ∃ sigma tau : Ty,
    NumberedNumericDecoding.decodeType domain = some sigma ∧
    NumberedNumericDecoding.decodeType codomain = some tau ∧
    NumberedNumericDecoding.decodeType (arrowCode domain codomain) = some (.arrow sigma tau)

def ActualActivationCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5),
  (activationValue n arity v = 0 ∨ activationValue n arity v = 1) ∧
  (activationValue n arity v = 1 ↔ active n arity v) ∧
  (activationValue n arity v = 0 ↔ ¬ active n arity v)

def ActualExplicitActivation : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (window : Program 1) (typed : Program 3)
    (guard arrow : Program 2),
  (∀ v, evaluate window v = GuardCalibration.validWindowValue n v) →
  (∀ v, evaluate typed v = JointGammaTyped.typedValue n arity v) →
  (∀ v, evaluate guard v = JointGammaDomain.guardValue v) →
  (∀ v, evaluate arrow v = arrowValue v) →
  ∀ v, evaluate (activation window typed guard arrow) v = activationValue n arity v

def ActualActivationProgram : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  ∃ (window : Program 1) (typed : Program 3) (guard arrow : Program 2),
    (∀ v, evaluate window v = GuardCalibration.validWindowValue n v) ∧
    (∀ v, evaluate typed v = JointGammaTyped.typedValue n arity v) ∧
    (∀ v, evaluate guard v = JointGammaDomain.guardValue v) ∧
    (∀ v, evaluate arrow v = arrowValue v) ∧
    (∀ v, evaluate (activation window typed guard arrow) v = activationValue n arity v)

/-- No premise about an output, a canonical Context code, or source decoding. -/
def ActualDomainSuccess : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context domain codomain f a : Nat),
  let v := List.Vector.ofFn ![context,domain,codomain,f,a]
  active n arity v →
  resultOption n arity v = some (resultValue n arity v) ∧ successValue n arity v = 1 ∧
  JointGammaApplication.applicationValue n arity
    (List.Vector.ofFn ![context,domain,codomain,f,a,resultValue n arity v]) = 1

def ActualDomainResultCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context domain codomain f a z : Nat),
  let v := List.Vector.ofFn ![context,domain,codomain,f,a]
  active n arity v →
  (JointGammaApplication.applicationValue n arity
    (List.Vector.ofFn ![context,domain,codomain,f,a,z]) = 1 ↔ z = resultValue n arity v)

def ActualDomainResultTyped : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context domain codomain f a : Nat),
  let v := List.Vector.ofFn ![context,domain,codomain,f,a]
  active n arity v →
  JointGammaTyped.typedValue n arity
    (List.Vector.ofFn ![context,codomain,resultValue n arity v]) = 1 ∧
  JointGammaDomain.guardValue (List.Vector.ofFn ![f,resultValue n arity v]) = 1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationDomainTargets
