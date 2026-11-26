module

public import LogicLineages.NativeModule.PersistentMarking.DecisionSourceBasicProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionSourceMarkProof
open Spine NameBridge TypeSupport DecisionInventory DecisionPorts DecisionSourceUniverse

theorem markFacts (q r : Expr) (hm : mark q = some r) :
    (∀ ρ, ρ ∈ auxiliarySupport r → ρ ∈ auxiliarySupport q) ∧
    heads r = heads q ∧ (∀ n, freeOccurs n r = freeOccurs n q) ∧ r.type = q.type := by
  cases q with
  | free σ x => cases hm
  | bound σ i => cases hm
  | marked f τ bs es => simp only [mark,Option.some.injEq] at hm; subst r; exact ⟨fun _ h => h,rfl,fun _ => rfl,rfl⟩
  | head f bs =>
    simp only [mark,Option.some.injEq] at hm; subst r
    refine ⟨?_,by simp [heads,headsArgs],?_,rfl⟩
    · intro ρ h
      simp only [auxiliarySupport,auxiliaryArgs,List.mem_append,List.not_mem_nil,or_false] at h
      simp only [auxiliarySupport,List.mem_append]
      rcases h with (h|h)|h
      · exact Or.inl h
      · exact Or.inl (List.mem_append_left _ h)
      · exact Or.inr h
    · intro n; simp [freeOccurs,freeOccursArgs]
  | lam σ q =>
    cases hq : mark q with
    | none => simp [mark,hq] at hm
    | some v =>
      simp only [mark,hq,Option.map_some,Option.some.injEq] at hm; subst r
      obtain ⟨ht,hh,hn,ha⟩ := markFacts q v hq
      refine ⟨?_,hh,hn,by simp only [Expr.type,ha]⟩
      intro ρ h
      simp only [auxiliarySupport,List.mem_append,ha] at h ⊢
      rcases h with (h|h)|h
      · exact Or.inl (Or.inl h)
      · exact Or.inl (Or.inr h)
      · exact Or.inr (ht ρ h)
termination_by sizeOf q

theorem sourceMark : DecisionSourceTargets.SourceMark := by
  intro K V H Γ q r hu hm
  obtain ⟨ht,hh,hn,ha⟩ := markFacts q r hm
  exact ⟨fun ρ hρ => hu.1 ρ (ht ρ hρ),fun f hf => hu.2.1 f (hh ▸ hf),fun n h => hu.2.2 n ((hn n) ▸ h)⟩

theorem sourceRetype : DecisionSourceTargets.SourceRetype := by
  intro K V H Γ f σ τ bs es hk hu hσ
  refine ⟨?_,hu.2.1,hu.2.2⟩
  intro ρ hρ
  simp only [auxiliarySupport,List.mem_append] at hρ
  rcases hρ with ((hd|hs)|hb)|he
  · exact hu.1 ρ (List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hd)))
  · exact hk σ hσ ρ hs
  · exact hu.1 ρ (List.mem_append_left _ (List.mem_append_right _ hb))
  · exact hu.1 ρ (List.mem_append_right _ he)
end LogicLineages.PersistentMarking.DecisionSourceMarkProof
