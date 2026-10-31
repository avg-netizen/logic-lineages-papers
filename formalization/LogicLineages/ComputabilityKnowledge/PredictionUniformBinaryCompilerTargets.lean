module
public import LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompilerDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompilerTargets
open Turing PredictionUniformBinaryCompiler

def PhysicalBinaryReadout : Prop :=
  ∀ (n : Nat) (b : Bool), readBit n = some b ↔ n = PredictionFiniteAlphabet.inputSymbol b

def EffectiveFixedBodyCompiler : Prop :=
  ∀ c : Turing.ToPartrec.Code, Primrec (compile c)

def UniversalBinaryCompiler : Prop :=
  ∃ f : Nat → Nat, Primrec f ∧ ∀ (e : Nat) (xs : List Bool) (b : Bool),
    b ∈ binaryEval (f e) xs ↔
      b.toNat ∈ (Nat.Partrec.Code.ofNatCode e).eval (Encodable.encode xs)

end LogicLineages.ComputabilityKnowledge.PredictionUniformBinaryCompilerTargets
