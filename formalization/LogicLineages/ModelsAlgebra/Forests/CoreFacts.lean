module

public import LogicLineages.ModelsAlgebra.Forests.CoreDefinitions

@[expose] public section

namespace LogicLineages.ModelsAlgebra.Forests.Core

universe u v

variable {α : Type u} {β : Type v} {r : α → α → Prop} {s : β → β → Prop}

theorem incomparable_no_common_upper (h : PredChain r) {x y : α}
    (hxy : Incomparable r x y) : ¬ ∃ z, r x z ∧ r y z := by
  intro hw
  exact hw.elim (fun _ hz => (h hz.1 hz.2).elim hxy.1 hxy.2)

theorem predChain_pullback (f : α → β) (hf : InducedEmbedding r s f)
    (h : PredChain s) : PredChain r := by
  intro x y z hxz hyz
  exact (h ((hf.2 x z).mpr hxz) ((hf.2 y z).mpr hyz)).elim
    (fun hxy => Or.inl ((hf.2 x y).mp hxy))
    (fun hyx => Or.inr ((hf.2 y x).mp hyx))

theorem comparableAdj_symmetric {x y : α} :
    ComparableAdj r x y → ComparableAdj r y x := by
  intro h
  exact ⟨fun heq => h.1 heq.symm, h.2.elim Or.inr Or.inl⟩

theorem comparableAdj_irreflexive (x : α) : ¬ ComparableAdj r x x := by
  intro h
  exact h.1 rfl

theorem comparableAdj_embedding (f : α → β) (hf : InducedEmbedding r s f) :
    InducedEmbedding (ComparableAdj r) (ComparableAdj s) f := by
  refine ⟨hf.1, ?_⟩
  intro x y
  constructor
  · intro h
    refine ⟨fun heq => h.1 (congrArg f heq), ?_⟩
    exact h.2.elim
      (fun hxy => Or.inl ((hf.2 x y).mp hxy))
      (fun hyx => Or.inr ((hf.2 y x).mp hyx))
  · intro h
    refine ⟨fun heq => h.1 (hf.1 heq), ?_⟩
    exact h.2.elim
      (fun hxy => Or.inl ((hf.2 x y).mpr hxy))
      (fun hyx => Or.inr ((hf.2 y x).mpr hyx))

end LogicLineages.ModelsAlgebra.Forests.Core
