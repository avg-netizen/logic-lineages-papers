module

public import LogicLineages.NativeModule.PersistentMarking.MarkedConstructorTargets

@[expose] public section

namespace LogicLineages.PersistentMarking.MarkedConstructorSelectProof
open Spine NameBridge DecisionPorts FiniteDomainFoundation HereditaryDomainCode MarkedConstructorTargets

theorem prefix_nonempty {σ τ : Ty} {ds : List Ty}
    (h : (ds,τ) ∈ fullPrefixes σ) : ds ≠ [] := by
  cases ds with
  | nil => cases σ <;> simp [fullPrefixes] at h
  | cons => simp

theorem selected_nonempty E heads M p a ds t (hn : ds ≠ []) :
    MarkedConstructorTests.selected E heads M p a ds t = true ↔
    ∃ xs, MarkedConstructorTests.ownerTuple E heads M p ds = some xs ∧
      (HereditaryDomainSemantics.decode E p.2.1 p.2.2.1
        (StructuralActions.fullAction E a.1 p.2.2.1 a.2 ds p.2.1 xs)).weak p.2.2.1 t = true := by
  cases ds with
  | nil => exact False.elim (hn rfl)
  | cons σ ds =>
    cases h : MarkedConstructorTests.ownerTuple E heads M p (σ::ds) <;>
      simp [MarkedConstructorTests.selected,h]

theorem select : MarkedConstructorTargets.SelectExact := by
  intro E heads M p t
  simp only [MarkedConstructorTests.selectTest,List.any_eq_true,Bool.and_eq_true,
    decide_eq_true_eq,List.mem_cons]
  constructor
  · rintro ⟨a,ha,suffix,hs,ht,hb⟩
    refine ⟨a,ha,?_⟩
    rcases hs with hs | hs
    · subst suffix
      exact Or.inl ⟨ht,hb⟩
    · obtain ⟨ds,τ⟩ := suffix
      dsimp at ht
      subst τ
      obtain ⟨xs,hxs,hbit⟩ := (selected_nonempty E heads M p a ds t (prefix_nonempty hs)).mp hb
      exact Or.inr ⟨ds,xs,hs,hxs,hbit⟩
  · rintro ⟨a,ha,h⟩
    refine ⟨a,ha,?_⟩
    rcases h with ⟨ht,hb⟩ | ⟨ds,xs,hs,hxs,hb⟩
    · exact ⟨([],a.1),Or.inl rfl,ht,hb⟩
    · exact ⟨(ds,p.2.1),Or.inr hs,rfl,
        (selected_nonempty E heads M p a ds t (prefix_nonempty hs)).mpr ⟨xs,hxs,hb⟩⟩
end LogicLineages.PersistentMarking.MarkedConstructorSelectProof
