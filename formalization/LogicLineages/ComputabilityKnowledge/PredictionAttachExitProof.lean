module
public import LogicLineages.ComputabilityKnowledge.PredictionAttachExitTargets
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.PredictionAttachExit
open StateTransition Relation

theorem bridgeStep : Targets.BridgeStep := by
  intro α β f g exit a h
  simp [step, h]

theorem rightPhase : Targets.RightPhase := by
  intro α β f g exit b
  apply tr_eval' g (step f g exit) Sum.inr
  intro a a' h
  subst a'
  cases hg : g a with
  | none => simp [hg, step]
  | some c =>
    simp only [hg]
    exact ⟨Sum.inr c, rfl, TransGen.single (by simp [step, hg])⟩

private theorem left_mem {α β : Type} (f : α → Option α) (g : β → Option β) (exit : α → β)
    {a : α} {result : α ⊕ β} (h : result ∈ eval (step f g exit) (.inl a)) :
    ∃ terminal, terminal ∈ eval f a ∧ result ∈ (Sum.inr <$> eval g (exit terminal)) := by
  let C : α ⊕ β → Prop := fun s => match s with
    | .inl a => ∃ terminal, terminal ∈ eval f a ∧ result ∈ (Sum.inr <$> eval g (exit terminal))
    | .inr b => result ∈ (Sum.inr <$> eval g b)
  have hgen : ∀ s, result ∈ eval (step f g exit) s → C s := by
    intro s hs
    apply evalInduction (C := C) hs
    intro s hs ih
    cases s with
    | inr b =>
      change result ∈ (Sum.inr <$> eval g b)
      rw [rightPhase α β f g exit b] at hs
      exact hs
    | inl a =>
      change ∃ terminal, terminal ∈ eval f a ∧ result ∈ (Sum.inr <$> eval g (exit terminal))
      cases hf : f a with
      | none =>
        have hr := ih (.inr (exit a)) (by simp [step, hf])
        exact ⟨a, mem_eval.mpr ⟨ReflTransGen.refl, hf⟩, hr⟩
      | some a' =>
        obtain ⟨terminal, ht, hr⟩ := ih (.inl a') (by simp [step, hf])
        obtain ⟨hrch, hnone⟩ := mem_eval.mp ht
        exact ⟨terminal, mem_eval.mpr ⟨ReflTransGen.head hf hrch, hnone⟩, hr⟩
  exact hgen (.inl a) h

theorem fullComposition : Targets.FullComposition := by
  intro α β f g exit a
  apply Part.ext
  intro result
  constructor
  · intro h
    obtain ⟨terminal, ht, hr⟩ := left_mem f g exit h
    obtain ⟨b, hb, hbr⟩ := (Part.mem_map_iff Sum.inr).mp hr
    exact (Part.mem_map_iff Sum.inr).mpr ⟨b, Part.mem_bind_iff.mpr ⟨terminal, ht, hb⟩, hbr⟩
  · intro h
    obtain ⟨b, hb, hbr⟩ := (Part.mem_map_iff Sum.inr).mp h
    obtain ⟨terminal, ht, hgb⟩ := Part.mem_bind_iff.mp hb
    obtain ⟨hrch, hnone⟩ := mem_eval.mp ht
    have hleft : Reaches (step f g exit) (.inl a) (.inl terminal) :=
      ReflTransGen.lift Sum.inl (fun x y hxy => by
        have heq : f x = some y := hxy
        simp [step, heq]) hrch
    have hbridge : Reaches (step f g exit) (.inl a) (.inr (exit terminal)) :=
      hleft.tail (bridgeStep α β f g exit terminal hnone)
    rw [reaches_eval hbridge, rightPhase α β f g exit (exit terminal)]
    exact (Part.mem_map_iff Sum.inr).mpr ⟨b, hgb, hbr⟩
end LogicLineages.ComputabilityKnowledge.PredictionAttachExit
