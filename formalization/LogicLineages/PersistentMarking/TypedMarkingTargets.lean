import LogicLineages.PersistentMarking.Typing
namespace LogicLineages.PersistentMarking.TypedMarkingTargets

def AnnotationExact : Prop := ∀ Γ s σ, Typed Γ s σ → s.type = σ
def PartialPreserves : Prop := ∀ Γ s σ, Typed Γ s σ →
  ∀ t, s.mark = some t → Typed Γ t σ
def TotalPreserves : Prop := ∀ Γ s σ, Typed Γ s σ → Typed Γ s.headmark σ
end LogicLineages.PersistentMarking.TypedMarkingTargets
