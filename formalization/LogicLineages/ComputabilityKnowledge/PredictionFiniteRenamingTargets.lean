module
public import LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingDefinitions
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingTargets
open Turing PredictionFiniteRenaming

def EffectiveNumericMaps : Prop :=
  ∀ (α : Type) [Primcodable α] [Inhabited α] [DecidableEq α],
    Primrec (fun z : List α × α => index z.1 z.2) ∧
    Primrec (fun z : List α × Nat => value z.1 z.2)

def InverseOnEnumeration : Prop :=
  ∀ (α : Type) [Inhabited α] [DecidableEq α] (tail : List α) (x : α),
    x ∈ items tail → decode tail (encode tail x) = x

def ExactRenamedStep : Prop :=
  ∀ (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] [DecidableEq Γ] [DecidableEq Λ]
    (m : TM0.Machine Γ Λ) (states : List Λ) (alphabet : List Γ),
    (∀ a : Γ, a ∈ items alphabet) → ∀ c : TM0.Cfg Γ Λ,
    c.q ∈ items states →
      (TM0.step m c).map (TM0.Cfg.map (toFinite alphabet) (toFinite states)) =
        TM0.step (renamed m states alphabet) (c.map (toFinite alphabet) (toFinite states))

def ExactSupportedSimulation : Prop :=
  ∀ (Γ Λ : Type) [Inhabited Γ] [Inhabited Λ] [DecidableEq Γ] [DecidableEq Λ]
    (m : TM0.Machine Γ Λ) (states : List Λ) (alphabet : List Γ),
    TM0.Supports m {s | s ∈ items states} → (∀ a : Γ, a ∈ items alphabet) →
    StateTransition.Respects (TM0.step m) (TM0.step (renamed m states alphabet))
      (fun c d => c.q ∈ items states ∧ c.map (toFinite alphabet) (toFinite states) = d)

end LogicLineages.ComputabilityKnowledge.PredictionFiniteRenamingTargets
