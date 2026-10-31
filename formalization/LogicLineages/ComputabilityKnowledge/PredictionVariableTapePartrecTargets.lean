module
public import LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecTargets
open PredictionVariableTapePartrec

def EffectiveBinaryObservation : Prop :=
  Primrec (fun z : Nat × Nat × List Bool => observation z.1 z.2.1 z.2.2)

def UniformBinaryCompiler : Prop :=
  ∃ u : Nat.Partrec.Code, Primrec (compile u) ∧ ∀ (code : Nat) (xs : List Bool) (v : Nat),
    v ∈ Nat.Partrec.Code.eval (compile u code) (Encodable.encode xs) ↔ Produces code xs v

def TotalBinaryCorrespondence : Prop :=
  ∃ u : Nat.Partrec.Code, Primrec (compile u) ∧
    (∀ (code : Nat) (xs : List Bool) (v : Nat),
      v ∈ Nat.Partrec.Code.eval (compile u code) (Encodable.encode xs) ↔ Produces code xs v) ∧
    ∀ code : Nat, PredictionLearning.TotalBinary (compile u code) ↔ PredictionTapeObservation.TotalBinary code

end LogicLineages.ComputabilityKnowledge.PredictionVariableTapePartrecTargets
