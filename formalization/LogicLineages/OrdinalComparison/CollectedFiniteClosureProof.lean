module
public import LogicLineages.OrdinalComparison.CollectedFiniteClosureTargets

@[expose] public section
namespace LogicLineages.OrdinalComparison

private theorem self_mem_closure (A : CollectedPositiveNF) : A∈collectedFormClosure A := by
  cases A
  exact List.mem_cons_self

mutual
  private theorem form_closure_valid (F : CollectedPositiveNF) (hv : CollectedPositiveValid F) :
      ∀ A∈collectedFormClosure F, CollectedPositiveValid A := by
    cases F with
    | mk c b tags =>
      intro A hm
      rcases List.mem_cons.mp hm with h | h
      · subst A; exact hv
      · exact tag_closure_valid tags hv A h
  private theorem tag_closure_valid (tags : CollectedPositiveTags) (hv : CollectedTagsValid tags) :
      ∀ A∈collectedTagFormClosure tags, CollectedPositiveValid A := by
    cases tags with
    | nil => simp [collectedTagFormClosure]
    | cons rho B b rest =>
      intro A hm
      rcases List.mem_append.mp hm with h | h
      · exact form_closure_valid B hv.2.2.1 A h
      · exact tag_closure_valid rest hv.2.2.2.2.2.2 A h
end

mutual
  private theorem form_closure_transitive (F : CollectedPositiveNF) (A : CollectedPositiveNF)
      (hA : A∈collectedFormClosure F) : ∀ B∈collectedFormClosure A, B∈collectedFormClosure F := by
    cases F with
    | mk c b tags =>
      rcases List.mem_cons.mp hA with h | h
      · subst A; intro B hB; exact hB
      · intro B hB
        exact List.mem_cons_of_mem _ (tag_closure_transitive tags A h B hB)
  private theorem tag_closure_transitive (tags : CollectedPositiveTags) (A : CollectedPositiveNF)
      (hA : A∈collectedTagFormClosure tags) : ∀ B∈collectedFormClosure A, B∈collectedTagFormClosure tags := by
    cases tags with
    | nil => simp [collectedTagFormClosure] at hA
    | cons rho F a rest =>
      intro B hB
      rcases List.mem_append.mp hA with h | h
      · exact List.mem_append_left _ (form_closure_transitive F A h B hB)
      · exact List.mem_append_right _ (tag_closure_transitive rest A h B hB)
end

private theorem direct_mem_closure (tags : CollectedPositiveTags) (rho : NONote) (A : CollectedPositiveNF)
    (hm : (rho,A)∈collectedDirectTags tags) : A∈collectedTagFormClosure tags := by
  cases tags with
  | nil => simp [collectedDirectTags] at hm
  | cons sigma B b rest =>
    rcases List.mem_cons.mp hm with h | h
    · cases h
      exact List.mem_append_left _ (self_mem_closure A)
    · exact List.mem_append_right _ (direct_mem_closure rest rho A h)
termination_by tags

private theorem direct_height (tags : CollectedPositiveTags) (rho : NONote) (A : CollectedPositiveNF)
    (hm : (rho,A)∈collectedDirectTags tags) : collectedPositiveHeight A<collectedTagsHeight tags := by
  cases tags with
  | nil => simp [collectedDirectTags] at hm
  | cons sigma B b rest =>
    rcases List.mem_cons.mp hm with h | h
    · cases h
      exact (Nat.lt_succ_self _).trans_le (le_max_left _ _)
    · exact (direct_height rest rho A h).trans_le (le_max_right _ _)
termination_by tags

private theorem direct_reachable (tags : CollectedPositiveTags) (rho : NONote) (A : CollectedPositiveNF)
    (hm : (rho,A)∈collectedDirectTags tags) : (rho,A)∈collectedNestedTags tags := by
  cases tags with
  | nil => simp [collectedDirectTags] at hm
  | cons sigma B b rest =>
    rcases List.mem_cons.mp hm with h | h
    · cases h; exact List.mem_cons_self
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (direct_reachable rest rho A h))
termination_by tags

theorem collectedFiniteClosureDomain : Targets.CollectedFiniteClosureDomain := by
  intro forms hv
  refine ⟨List.mem_cons_self,?_,?_,?_⟩
  · intro A hA
    exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr ⟨A,hA,self_mem_closure A⟩)
  · intro A hA
    rcases List.mem_cons.mp hA with h | h
    · subst A; trivial
    · rcases List.mem_flatMap.mp h with ⟨F,hF,hAF⟩
      exact form_closure_valid F (hv F hF) A hAF
  · intro c b tags hA rho A hm
    rcases List.mem_cons.mp hA with h | h
    · cases h
      simp [collectedDirectTags] at hm
    · rcases List.mem_flatMap.mp h with ⟨F,hF,hAF⟩
      have hd : A∈collectedFormClosure (.mk c b tags) :=
        List.mem_cons_of_mem _ (direct_mem_closure tags rho A hm)
      exact List.mem_cons_of_mem _ (List.mem_flatMap.mpr
        ⟨F,hF,form_closure_transitive F (.mk c b tags) hAF A hd⟩)

theorem collectedDirectChildHeight : Targets.CollectedDirectChildHeight := by
  intro c b tags rho A hm
  exact direct_height tags rho A hm

theorem collectedDirectTagReachable : Targets.CollectedDirectTagReachable := by
  intro c b tags rho A hm
  exact direct_reachable tags rho A hm

end LogicLineages.OrdinalComparison
