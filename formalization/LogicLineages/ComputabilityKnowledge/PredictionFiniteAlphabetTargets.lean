module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetTargets
open Turing PredictionFiniteAlphabet

def EffectiveDecoding : Prop :=
  Primrec decodeTable ∧ ∀ p : Table, decodeTable (Encodable.encode p) = p

def EffectiveBoundedSimulation : Prop :=
  Primrec (fun z : Nat × Nat × List Bool => simulate z.1 z.2.1 z.2.2)

def ExactSingleStep : Prop :=
  ∀ (p : Table) (c : Raw),
    (step p c).map (toCfg p) = TM0.step (machine p) (toCfg p c)

def ExactBoundedSimulation : Prop :=
  ∀ (p : Table) (fuel : Nat) (c d : Raw), bounded p fuel c = some d ↔
    ∃ n : Nat, n < fuel ∧ Run p c d n ∧ step p d = none

def ExactInitialTape : Prop :=
  ∀ (p : Table) (xs : List Bool),
    toCfg p (initial p xs) =
      ⟨p.2.1, Tape.mk₁ (xs.map (fun b => symbol p (inputSymbol b)))⟩

def LiteralInputSymbols : Prop :=
  ∀ p : Table, (symbol p 0).val = 0 ∧
    (symbol p (inputSymbol false)).val = 1 ∧
    (symbol p (inputSymbol true)).val = 2

end LogicLineages.ComputabilityKnowledge.PredictionFiniteAlphabetTargets
