module
public import LogicLineages.ComputabilityKnowledge.PredictionTapePartrecDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionTapePartrecTargets
open PredictionTapeTable PredictionLearning PredictionTapePartrec

def EffectiveObservation : Prop :=
  Primrec (fun z : Nat × Nat × List Bool => observation z.1 z.2.1 z.2.2)

def OperationalObservation : Prop :=
  ∀ (code : Nat) (xs : List Bool) (v : Nat),
    (∃ fuel : Nat, observation code fuel xs = some v) ↔ Produces code xs v

/-- One fixed ordinary universal program and its explicit primitive-recursive
curry compiler realize all natural-indexed tape tables, including malformed
indices and nonbinary halts, with exact partial output semantics. -/
def UniformOperationalCompiler : Prop :=
  ∃ universal : Code, Primrec (compile universal) ∧
    ∀ (code : Nat) (xs : List Bool) (v : Nat),
      v ∈ Nat.Partrec.Code.eval (compile universal code) (Encodable.encode xs) ↔
        Produces code xs v

def TotalBinaryCorrespondence : Prop :=
  ∃ universal : Code, Primrec (compile universal) ∧
    (∀ (code : Nat) (xs : List Bool) (v : Nat),
      v ∈ Nat.Partrec.Code.eval (compile universal code) (Encodable.encode xs) ↔
        Produces code xs v) ∧
    ∀ code : Nat, TotalBinary (compile universal code) ↔
      ∀ xs : List Bool, ∃ b : Bool, Produces code xs (bitValue b)

end LogicLineages.ComputabilityKnowledge.PredictionTapePartrecTargets
