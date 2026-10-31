module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelExplicitCodecDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelExplicitCodec.Targets
open PredictionCompilerFinitePayloadCodec

def Roundtrip : Prop := ∀ q : Label, decode (code q) = q
def FoldCorrect : Prop := ∀ (α : Type) (z : α) (step : Nat → Nat → Quint α → α) (q : Label),
  fold z step (code q) = termFold z step q
def FoldPrimitiveRecursive : Prop := ∀ (α : Type) [Primcodable α] (z : α)
  (step : Nat → Nat → Quint α → α),
  Primrec (fun p : Nat × Nat × Quint α => step p.1 p.2.1 p.2.2) → Primrec (fold z step)
def NormalizationPrimitiveRecursive : Prop := Primrec normalize
def ActualPrimcodable : Prop := ∃ i : Primcodable Label, @Encodable.encode Label i.toEncodable = code
end LogicLineages.ComputabilityKnowledge.PredictionCompilerSourceLabelExplicitCodec.Targets
