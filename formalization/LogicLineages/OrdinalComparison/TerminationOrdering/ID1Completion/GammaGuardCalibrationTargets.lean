module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationTargets
open GammaGuardCalibration
open LogicLineages.ComputabilityKnowledge.GorbowPRProgram

def ActualGammaPrimitive : Prop := Primrec gammaCode

def ActualGammaProgram : Prop :=
  ∃ p : Program 1, ∀ v, evaluate p v = gammaValue v

def ActualValidityEvaluation : Prop :=
  ∀ (p : Program 2) (v : List.Vector Nat 1),
    evaluate (validity p) v = evaluate p (List.Vector.ofFn ![v.get 0,v.get 0])

def ActualValidityCalibration : Prop :=
  ∀ (p : Program 2), (∀ v, evaluate p v = JointGammaDomain.guardValue v) →
    ∀ v, evaluate (validity p) v = objectValid (v.get 0)

def ActualGuardRange : Prop :=
  ∀ v : List.Vector Nat 2,
    JointGammaDomain.guardValue v = 0 ∨ JointGammaDomain.guardValue v = 1

def ActualGuardCalibration : Prop :=
  ∀ x u : Nat, JointGammaDomain.guardValue (List.Vector.ofFn ![x,u]) = 1 ↔
    objectValid x = 1 ∧ objectValid u = 1 ∧ gammaCode x = gammaCode u

def ActualTypedValid : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (c t x : Nat),
    JointGammaTyped.typedValue n arity (List.Vector.ofFn ![c,t,x]) = 1 → objectValid x = 1

def ActualPositiveGamma : Prop :=
  ∀ (n : Nat) (arity : Fin n → Nat) (c x y k : Nat),
    ContextUniform.positiveValue n arity (List.Vector.ofFn ![c,x,y,k]) = 1 →
      gammaCode x = gammaCode y

def ActualObjectValidity : Prop :=
  ∀ x : Nat, objectValid x = 1 ↔
    ∃ obj : ContextUniform.Object, Encodable.decode x = some obj

def ActualGammaDecoded : Prop :=
  ∀ (x : Nat) (obj : ContextUniform.Object),
    Encodable.decode x = some obj → gammaCode x = Encodable.encode obj.1

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.GammaGuardCalibrationTargets
