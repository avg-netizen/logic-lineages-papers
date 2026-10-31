module
public import LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationCodecDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationCodec.Targets

def ListRoundtrip : Prop := (∀ k, fromList (toList k) = k) ∧ (∀ xs, toList (fromList xs) = xs)
def Roundtrip : Prop := ∀ k, decode (code k) = k
def FoldCorrect : Prop := ∀ (α : Type) (z : α) (step : Frame → α → α) (k : Cont),
  (toList k).foldr step z = fold z step k
def ActualPrimcodable : Prop := ∃ i : Primcodable Cont, @Encodable.encode Cont i.toEncodable = code

def FoldPrimitiveRecursive : Prop := ∀ (i : Primcodable Cont),
  @Encodable.encode Cont i.toEncodable = code →
    ∀ (α : Type) [Primcodable α] (z : α) (step : Frame → α → α),
      Primrec₂ step → @Primrec Cont α i _ (fold z step)
end LogicLineages.ComputabilityKnowledge.PredictionSequentialContinuationCodec.Targets
