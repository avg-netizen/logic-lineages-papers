module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationEffectivityDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationEffectivity.Targets
open PredictionSequentialContinuationCodec

def ListPrimitiveRecursive : Prop := Primrec toList ∧ Primrec fromList

def ConstructorPrimitiveRecursive : Prop := Primrec₂ Turing.PartrecToTM2.Cont'.cons₁ ∧
  Primrec Turing.PartrecToTM2.Cont'.cons₂ ∧ Primrec₂ Turing.PartrecToTM2.Cont'.comp ∧
  Primrec₂ Turing.PartrecToTM2.Cont'.fix

def DecodePrimitiveRecursive : Prop := Primrec decode

def CasesPrimitiveRecursive : Prop := ∀ (α : Type) [Primcodable α] (z : α) (step : Frame → Cont → α),
  Primrec₂ step → Primrec (cases z step)
end LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationEffectivity.Targets
