module
public import LogicLineages.OrdinalComparison.SourceLocatedSubtermsTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceLocatedSubtermsProof
open SourceLocatedSubterms SourceLocatedSubtermsTargets SourceTypeSupport

theorem locatedRootMembership : LocatedRootMembership := by
  intro Symbol arity Ξ Λ τ t
  cases t <;> exact List.mem_cons_self

private theorem children_mem {Symbol : Type} {arity : Symbol → Nat}
    (u v : LocatedTerm Symbol arity) (hv : v ∈ children u) :
    v ∈ collect u.binders u.body := by
  rcases u with ⟨Λ, Ξ, τ, t⟩
  cases t with
  | var | zeroC | succC | caseC | recC => cases hv
  | app f a =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (locatedRootMembership _ _ _ _ _ f))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (locatedRootMembership _ _ _ _ _ a))
  | lam body =>
    rename_i σ τ
    have he : v = ⟨σ :: Λ, _, _, body⟩ := by simpa [children] using hv
    subst v
    exact List.mem_cons_of_mem _ (locatedRootMembership _ _ _ _ _ body)
  | ranked s args =>
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hv
    exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨collect Λ (args i),
      List.mem_ofFn.mpr ⟨i, rfl⟩, locatedRootMembership _ _ _ _ _ (args i)⟩)

private theorem subtree_mem {Symbol : Type} {arity : Symbol → Nat} {Ξ : List Ty} {τ : Ty}
    (t : Term Symbol arity Ξ τ) : ∀ Λ (u v : LocatedTerm Symbol arity),
    u ∈ collect Λ t → v ∈ collect u.binders u.body → v ∈ collect Λ t := by
  induction t with
  | var | zeroC | succC | caseC | recC =>
    intro Λ u v hu hv
    rcases List.mem_cons.mp hu with rfl | h
    · exact hv
    · cases h
  | app f a ihf iha =>
    intro Λ u v hu hv
    rcases List.mem_cons.mp hu with rfl | h
    · exact hv
    rcases List.mem_append.mp h with h | h
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihf Λ u v h hv))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (iha Λ u v h hv))
  | lam body ih =>
    intro Λ u v hu hv
    rcases List.mem_cons.mp hu with rfl | h
    · exact hv
    · exact List.mem_cons_of_mem _ (ih (_ :: Λ) u v h hv)
  | ranked s args ih =>
    intro Λ u v hu hv
    rcases List.mem_cons.mp hu with rfl | h
    · exact hv
    obtain ⟨l, hl, hu⟩ := List.mem_flatten.mp h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact List.mem_cons_of_mem _ (List.mem_flatten.mpr ⟨collect Λ (args i),
      List.mem_ofFn.mpr ⟨i, rfl⟩, ih i Λ u v hu hv⟩)

theorem locatedChildClosure : LocatedChildClosure := by
  intro Symbol arity Ξ Λ τ t u v hu hv
  exact subtree_mem t Λ u v hu (children_mem u v hv)

theorem locatedTypeSupport : LocatedTypeSupport := by
  intro Symbol arity Ξ Λ τ t
  induction t generalizing Λ with
  | var | zeroC | succC | caseC | recC =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact Finset.Subset.rfl
    · cases h
  | app f a ihf iha =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact Finset.Subset.rfl
    rcases List.mem_append.mp h with h | h
    · intro σ hσ
      exact Finset.mem_union_right _ (Finset.mem_union_left _ (ihf Λ u h hσ))
    · intro σ hσ
      exact Finset.mem_union_right _ (Finset.mem_union_right _ (iha Λ u h hσ))
  | lam body ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact Finset.Subset.rfl
    · intro σ hσ
      exact Finset.mem_union_right _ (ih (_ :: Λ) u h hσ)
  | ranked s args ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact Finset.Subset.rfl
    obtain ⟨l, hl, hu⟩ := List.mem_flatten.mp h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    intro σ hσ
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ih i Λ u hu hσ⟩)

theorem locatedDepthBudget : LocatedDepthBudget := by
  intro Symbol arity Ξ Λ τ t
  induction t generalizing Λ with
  | var | zeroC | succC | caseC | recC =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact le_rfl
    · cases h
  | app f a ihf iha =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact le_rfl
    rcases List.mem_append.mp h with h | h
    · exact (ihf Λ u h).trans (Nat.add_le_add_left (Nat.le_max_left _ _) _)
    · exact (iha Λ u h).trans (Nat.add_le_add_left (Nat.le_max_right _ _) _)
  | lam body ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact le_rfl
    · have hh := ih (_ :: Λ) u h
      simpa only [List.length_cons, lambdaDepth, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hh
  | ranked s args ih =>
    intro u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact le_rfl
    obtain ⟨l, hl, hu⟩ := List.mem_flatten.mp h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact (ih i Λ u hu).trans (Nat.add_le_add_left (Finset.le_sup (f := fun j => lambdaDepth (args j)) (Finset.mem_univ i)) _)

theorem locatedContextCalibration : LocatedContextCalibration := by
  intro Symbol arity Ξ Λ Γ τ t
  induction t generalizing Λ with
  | var | zeroC | succC | caseC | recC =>
    intro he u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact he
    · cases h
  | app f a ihf iha =>
    intro he u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact he
    rcases List.mem_append.mp h with h | h
    · exact ihf Λ he u h
    · exact iha Λ he u h
  | lam body ih =>
    intro he u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact he
    · exact ih (_ :: Λ) (congrArg (List.cons _) he) u h
  | ranked s args ih =>
    intro he u hu
    rcases List.mem_cons.mp hu with rfl | h
    · exact he
    obtain ⟨l, hl, hu⟩ := List.mem_flatten.mp h
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hl
    exact ih i Λ he u hu

end LogicLineages.OrdinalComparison.Source.SourceLocatedSubtermsProof
