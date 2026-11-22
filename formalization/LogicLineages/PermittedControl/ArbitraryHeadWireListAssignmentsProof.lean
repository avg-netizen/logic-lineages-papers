module
public import LogicLineages.PermittedControl.ArbitraryHeadWireListTargets

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryHeadWireList
open ArbitraryHeadSharedWire (Valuation)

theorem hiddenMember {gates : List Gate} {g : Gate} (hg : g ∈ gates) (inf : g.finite = false) :
    g.hidden ∈ hiddenNames gates := by
  exact List.mem_filterMap.mpr ⟨g,hg,by simp only [Gate.hiddenName,inf]⟩

private theorem memberHidden {gates : List Gate} {n : Nat} (mem : n ∈ hiddenNames gates) :
    ∃ g ∈ gates, g.finite = false ∧ g.hidden = n := by
  obtain ⟨g,hg,name⟩ := List.mem_filterMap.mp mem
  cases hf : g.finite with
  | false => exact ⟨g,hg,hf,Option.some.inj (by simpa only [Gate.hiddenName,hf] using name)⟩
  | true => simp [Gate.hiddenName,hf] at name

private theorem namesFinite (g : Gate) (gs : List Gate) (hf : g.finite = true) :
    hiddenNames (g :: gs) = hiddenNames gs := by
  simp [hiddenNames,Gate.hiddenName,hf]

private theorem namesInfinite (g : Gate) (gs : List Gate) (hf : g.finite = false) :
    hiddenNames (g :: gs) = g.hidden :: hiddenNames gs := by
  simp [hiddenNames,Gate.hiddenName,hf]

theorem extendAgrees (gates : List Gate) (ν : Valuation) :
    Agrees gates ν (extend ν gates) := by
  induction gates with
  | nil => intro n _; rfl
  | cons g gs ih =>
      intro n hn
      cases hf : g.finite with
      | true =>
          rw [namesFinite g gs hf] at hn
          simpa only [extend,hf] using ih n hn
      | false =>
          rw [namesInfinite g gs hf] at hn
          have diff : n ≠ g.hidden := by
            intro same
            subst n
            exact hn List.mem_cons_self
          have avoid : n ∉ hiddenNames gs := fun h => hn (List.mem_cons_of_mem _ h)
          simpa only [extend,hf,Function.update_of_ne diff] using ih n avoid

theorem extendPrescribed (gates : List Gate) (ν : Valuation) (nd : (hiddenNames gates).Nodup) :
    Prescribed gates ν (extend ν gates) := by
  induction gates with
  | nil => intro g hg; simp at hg
  | cons p ps ih =>
      intro g hg inf
      cases hp : p.finite with
      | true =>
          rw [namesFinite p ps hp] at nd
          rcases List.mem_cons.mp hg with he | ht
          · subst g
            rw [inf] at hp
            cases hp
          · simpa only [extend,hp] using ih nd g ht inf
      | false =>
          rw [namesInfinite p ps hp] at nd
          have hn := List.nodup_cons.mp nd
          rcases List.mem_cons.mp hg with he | ht
          · subst g
            simp only [extend,hp,Function.update_self]
          · have diff : g.hidden ≠ p.hidden := by
              intro eq
              apply hn.1
              rw [← eq]
              exact hiddenMember ht inf
            simpa only [extend,hp,Function.update_of_ne diff] using ih hn.2 g ht inf

theorem exactWireListAssignments : ExactWireListAssignments := by
  intro gates ν θ nd
  constructor
  · rintro ⟨agrees,assigned⟩
    funext n
    by_cases mem : n ∈ hiddenNames gates
    · obtain ⟨g,hg,inf,he⟩ := memberHidden mem
      rw [← he]
      exact (assigned g hg inf).trans (extendPrescribed gates ν nd g hg inf).symm
    · exact (agrees n mem).trans (extendAgrees gates ν n mem).symm
  · rintro rfl
    exact ⟨extendAgrees gates ν,extendPrescribed gates ν nd⟩

end LogicLineages.PermittedControl.ArbitraryHeadWireList
