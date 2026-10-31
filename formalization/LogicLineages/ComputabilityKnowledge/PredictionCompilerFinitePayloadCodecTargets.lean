module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFinitePayloadCodecDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerFinitePayloadCodec.Targets
open Turing.PartrecToTM2

def GammaRoundtrip : Prop := (∀ g, bitsGamma (gammaBits g) = g) ∧ (∀ b, gammaBits (bitsGamma b) = b)
def StackRoundtrip : Prop := (∀ k, bitsStack (stackBits k) = k) ∧ (∀ b, stackBits (bitsStack b) = b)
def GammaTableRoundtrip : Prop := ∀ (α : Type),
  (∀ f : Γ' → α, tableGamma (gammaTable f) = f) ∧ (∀ t : Quad α, gammaTable (tableGamma t) = t)
def StoreTableRoundtrip : Prop := ∀ (α : Type),
  (∀ f : Option Γ' → α, tableStore (storeTable f) = f) ∧ (∀ t : Quint α, storeTable (tableStore t) = t)
def ActualPrimcodable : Prop :=
  (∃ i : Primcodable Γ', @Encodable.encode Γ' i.toEncodable = fun g => Encodable.encode (gammaBits g)) ∧
  (∃ i : Primcodable K', @Encodable.encode K' i.toEncodable = fun k => Encodable.encode (stackBits k)) ∧
  (∀ (α : Type) [Primcodable α],
    ∃ i : Primcodable (Γ' → α), @Encodable.encode (Γ' → α) i.toEncodable = fun f => Encodable.encode (gammaTable f)) ∧
  (∀ (α : Type) [Primcodable α],
    ∃ i : Primcodable (Option Γ' → α), @Encodable.encode (Option Γ' → α) i.toEncodable = fun f => Encodable.encode (storeTable f))
end LogicLineages.ComputabilityKnowledge.PredictionCompilerFinitePayloadCodec.Targets
