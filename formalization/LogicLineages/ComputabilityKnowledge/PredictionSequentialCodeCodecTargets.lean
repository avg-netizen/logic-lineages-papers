module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodecDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodec.Targets

def Roundtrip : Prop := ∀ c : Code, decode (code c) = c

def FoldCorrect : Prop := ∀ (α : Type) (leaf : Nat → α) (branch : Nat → α → α → α) (c : Code),
  fold leaf branch (code c) = termFold leaf branch c

def FoldPrimitiveRecursive : Prop := ∀ (α : Type) [Primcodable α]
  (leaf : Nat → α) (branch : Nat → α → α → α),
  Primrec leaf → Primrec (fun p : Nat × α × α => branch p.1 p.2.1 p.2.2) → Primrec (fold leaf branch)

def NormalizationPrimitiveRecursive : Prop := Primrec normalize

def ActualPrimcodable : Prop := ∃ i : Primcodable Code, @Encodable.encode Code i.toEncodable = code
end LogicLineages.ComputabilityKnowledge.PredictionSequentialCodeCodec.Targets
