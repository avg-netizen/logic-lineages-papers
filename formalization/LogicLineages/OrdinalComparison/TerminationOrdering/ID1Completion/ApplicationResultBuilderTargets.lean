module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderTargets
open Source ApplicationResultBuilder
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualPartialCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context domain codomain f a z : Nat),
  resultOption n arity (List.Vector.ofFn ![context,domain,codomain,f,a]) = some z ↔
    JointGammaApplication.encodedApplication n arity context domain codomain f a z

def ActualPrimitive : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat),
  Primrec (resultOption n arity) ∧ Primrec (resultValue n arity) ∧ Primrec (successValue n arity)

def ActualTotalCalibration : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context domain codomain f a z : Nat),
  JointGammaApplication.applicationValue n arity
    (List.Vector.ofFn ![context,domain,codomain,f,a,z]) = 1 ↔
  successValue n arity (List.Vector.ofFn ![context,domain,codomain,f,a]) = 1 ∧
    z = resultValue n arity (List.Vector.ofFn ![context,domain,codomain,f,a])

def ActualSuccessAndDefault : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 5),
  (successValue n arity v = 0 ∨ successValue n arity v = 1) ∧
  (successValue n arity v = 0 ↔ resultOption n arity v = none) ∧
  (successValue n arity v = 0 → resultValue n arity v = 0)

def ActualOriginalRange : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (v : List.Vector Nat 6),
  JointGammaApplication.applicationValue n arity v = 0 ∨
    JointGammaApplication.applicationValue n arity v = 1

/-- Literal numeric equality for every input, not merely on genuine terms. -/
def ActualOriginalValue : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context domain codomain f a z : Nat),
  JointGammaApplication.applicationValue n arity
    (List.Vector.ofFn ![context,domain,codomain,f,a,z]) =
  if successValue n arity (List.Vector.ofFn ![context,domain,codomain,f,a]) = 1 ∧
      z = resultValue n arity (List.Vector.ofFn ![context,domain,codomain,f,a]) then 1 else 0

def ActualRawUniqueness : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (context domain codomain f a z w : Nat),
  JointGammaApplication.encodedApplication n arity context domain codomain f a z →
  JointGammaApplication.encodedApplication n arity context domain codomain f a w → z = w

/-- Two total primitive-recursive Programs chosen before all input codes. -/
def ActualProgramWitnesses : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat), ∃ result success : Program 5,
  (∀ v, evaluate result v = resultValue n arity v) ∧
  (∀ v, evaluate success v = successValue n arity v) ∧
  (∀ context domain codomain f a z : Nat,
    JointGammaApplication.applicationValue n arity
      (List.Vector.ofFn ![context,domain,codomain,f,a,z]) = 1 ↔
    evaluate success (List.Vector.ofFn ![context,domain,codomain,f,a]) = 1 ∧
      z = evaluate result (List.Vector.ofFn ![context,domain,codomain,f,a]))

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.ApplicationResultBuilderTargets
