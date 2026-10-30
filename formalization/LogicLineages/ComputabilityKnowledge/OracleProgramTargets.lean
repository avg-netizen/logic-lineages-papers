module

public import LogicLineages.ComputabilityKnowledge.OracleProgramDefinitions

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.OracleProgramTargets
open OracleProgram

def InjectiveProgramEncoding : Prop := Function.Injective encode

def OracleEvaluationSound : Prop :=
  ∀ (g : Nat → Part Nat) (p : Program), Nat.RecursiveIn {g} (eval g p)

def OracleEvaluationComplete : Prop :=
  ∀ (g f : Nat → Part Nat), Nat.RecursiveIn {g} f → ∃ p : Program, eval g p = f

def OrdinaryBaseCalibration : Prop :=
  ∀ (g : Nat → Part Nat) (c : Nat.Partrec.Code) (n : Nat), eval g (.base c) n = Nat.Partrec.Code.eval c n

def OracleSpecializationSemantics : Prop :=
  ∀ (g : Nat → Part Nat) (p : Program) (a x : Nat),
    eval g (specialize p a) x = eval g p (Nat.pair a x)

def UniformEncodedSpecialization : Prop :=
  Primrec₂ specializeIndex ∧ ∀ (p : Program) (a : Nat),
    specializeIndex (encode p) a = encode (specialize p a)

end LogicLineages.ComputabilityKnowledge.OracleProgramTargets
