module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationTargets
open Turing PredictionFiniteSerialization

def EffectiveFixedDimensionSerializer : Prop :=
  ∀ q a : Nat, Primrec (fun z : Fin (q + 1) × FinMachine q a => code z.1 z.2)

def ExactNumericLayout : Prop :=
  ∀ (q a : Nat) (start : Fin (q + 1)) (m : FinMachine q a),
    (table start m).1 = a ∧ (table start m).2.1 = start.val ∧
    (table start m).2.2.length = (q + 1) * (a + 3)

def ExactTransitionLookup : Prop :=
  ∀ (q a : Nat) (start : Fin (q + 1)) (m : FinMachine q a)
    (s : Fin (q + 1)) (b : Fin (a + 3)),
    PredictionFiniteAlphabet.lookup (table start m) s.val b.val =
      (m s b).map numericEntry

def ExactSerializedStep : Prop :=
  ∀ (q a : Nat) (start : Fin (q + 1)) (m : FinMachine q a)
    (c : TM0.Cfg (Fin (a + 3)) (Fin (q + 1))),
    TM0.step (PredictionFiniteAlphabet.machine (table start m)) (embedCfg c) =
      (TM0.step (finiteMachine m) c).map embedCfg

end LogicLineages.ComputabilityKnowledge.PredictionFiniteSerializationTargets
