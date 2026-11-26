module

public import LogicLineages.NativeModule.PersistentMarking.DecisionInventory

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionInventoryTargets
open Spine NameBridge TypeSupport DecisionInventory

def FreeInventoryExact : Prop := ∀ q name,
  name ∈ freeInventory q ↔ freeOccurs name q = true

def AuxiliaryContainsLiteral : Prop := ∀ q ρ,
  ρ ∈ support q → ρ ∈ auxiliarySupport q

def AuxiliaryContainsDeclarations : Prop := ∀ q f,
  f ∈ heads q → ∀ ρ, ρ ∈ declaration f → ρ ∈ auxiliarySupport q

def OrdinaryAuxiliaryExact : Prop := ∀ Γ q τ,
  Typed Γ q τ → Ordinary q → ∀ ρ,
    ρ ∈ auxiliarySupport q ↔ ρ ∈ support q

def RankedDeclarationExact : Prop := ∀ name arity ρ,
  ρ ∈ declaration (.ranked name arity) ↔ ρ = Ty.ground

def SubtypeClosed : Prop := ∀ q σ ρ,
  σ ∈ auxiliarySupport q → ρ ∈ subtypes σ → ρ ∈ auxiliarySupport q

def DepthExact : Prop := ∀ q n, LambdaPath q n → n ≤ lambdaDepth q

def DepthAttained : Prop := ∀ q, LambdaPath q (lambdaDepth q)

/- This is an input inventory bridge, NOT the recursive request closure lemma.
The latter must still pay actual port normalization and generated syntax. -/
def InputTypesExact : Prop := ∀ Γ Δ s t σ τ,
  Typed Γ s σ → Typed Δ t τ → Ordinary s → Ordinary t → ∀ ρ,
  ρ ∈ (inventory s t).types ↔ ρ ∈ auxiliarySupport s ∨ ρ ∈ auxiliarySupport t
end LogicLineages.PersistentMarking.DecisionInventoryTargets
