module
public import LogicLineages.ComputabilityKnowledge.PredictionCompilerFinitePayloadCodecTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionCompilerFinitePayloadCodec
open Turing.PartrecToTM2

theorem gammaRoundtrip : Targets.GammaRoundtrip := by
  constructor
  · intro g; cases g <;> rfl
  · rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

theorem stackRoundtrip : Targets.StackRoundtrip := by
  constructor
  · intro k; cases k <;> rfl
  · rintro ⟨a, b⟩; cases a <;> cases b <;> rfl

theorem gammaTableRoundtrip : Targets.GammaTableRoundtrip := by
  intro α
  constructor
  · intro f; funext g; cases g <;> rfl
  · rintro ⟨a,b,c,d⟩; rfl

theorem storeTableRoundtrip : Targets.StoreTableRoundtrip := by
  intro α
  constructor
  · intro f; funext g; cases g with
    | none => rfl
    | some g => cases g <;> rfl
  · rintro ⟨a,b,c,d,e⟩; rfl

def gammaEquiv : Γ' ≃ Bool × Bool := ⟨gammaBits, bitsGamma, gammaRoundtrip.1, gammaRoundtrip.2⟩
def stackEquiv : K' ≃ Bool × Bool := ⟨stackBits, bitsStack, stackRoundtrip.1, stackRoundtrip.2⟩
def gammaTableEquiv (α : Type) : (Γ' → α) ≃ Quad α :=
  ⟨gammaTable, tableGamma, (gammaTableRoundtrip α).1, (gammaTableRoundtrip α).2⟩
def storeTableEquiv (α : Type) : (Option Γ' → α) ≃ Quint α :=
  ⟨storeTable, tableStore, (storeTableRoundtrip α).1, (storeTableRoundtrip α).2⟩

instance gammaPrimcodable : Primcodable Γ' := Primcodable.ofEquiv (Bool × Bool) gammaEquiv
instance stackPrimcodable : Primcodable K' := Primcodable.ofEquiv (Bool × Bool) stackEquiv
instance gammaFunctionPrimcodable (α : Type) [Primcodable α] : Primcodable (Γ' → α) :=
  Primcodable.ofEquiv (Quad α) (gammaTableEquiv α)
instance storeFunctionPrimcodable (α : Type) [Primcodable α] : Primcodable (Option Γ' → α) :=
  Primcodable.ofEquiv (Quint α) (storeTableEquiv α)

theorem actualPrimcodable : Targets.ActualPrimcodable := by
  refine ⟨⟨gammaPrimcodable, rfl⟩, ⟨stackPrimcodable, rfl⟩, ?_, ?_⟩
  · intro α inst; exact ⟨gammaFunctionPrimcodable α, rfl⟩
  · intro α inst; exact ⟨storeFunctionPrimcodable α, rfl⟩
end LogicLineages.ComputabilityKnowledge.PredictionCompilerFinitePayloadCodec
