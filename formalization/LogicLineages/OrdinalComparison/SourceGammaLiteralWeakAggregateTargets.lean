module
public import LogicLineages.OrdinalComparison.SourceGammaLiteralWeakAggregateDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaLiteralWeakAggregate.Targets

def NumericGap : Prop := ∀ b l r : Nat,
  (SourceGammaCollision.g b (r+5) ≤ SourceGammaCollision.g b (l+3) ↔ r + 2 ≤ l)

def FiniteForestWeak : Prop :=
  (∀ (b : Nat) (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal)
    (es : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)),
    SourceGammaAggregate.FiniteLeaves b ν es →
    (WeakAt b ν es ↔ ¬SourceGammaAggregate.AllEqual b ν es)) ∧
  (∀ (b : Nat) (Γ : List Ty) (ν : OrdinalComponent Γ → Ordinal),
    ¬WeakAt b ν ([] : List (OriginalTerm Γ .ground × OriginalTerm Γ .ground)))

def UniversalNonhalting : Prop := ∀ b e : Nat,
  RawUniversalWeak b e ↔ ¬SourceBlankMachineSimulation.Halts e
end LogicLineages.OrdinalComparison.Source.SourceGammaLiteralWeakAggregate.Targets
