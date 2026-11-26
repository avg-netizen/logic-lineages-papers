module

public import LogicLineages.NativeModule.PersistentMarking.DecisionInventoryTargets
public import LogicLineages.NativeModule.PersistentMarking.TypeSupportFoundationProof

@[expose] public section

namespace LogicLineages.PersistentMarking.DecisionInventoryProof
open Spine NameBridge TypeSupport DecisionInventory
mutual
 theorem freeExact (q : Expr) (name : Name) : name ∈ freeInventory q ↔ freeOccurs name q = true := by
  cases q with
  | free σ x => simp [freeInventory,freeOccurs]
  | bound σ i => simp [freeInventory,freeOccurs]
  | lam σ q => exact freeExact q name
  | head f bs => exact freeExactArgs bs name
  | marked f τ bs es => simp only [freeInventory,freeOccurs,List.mem_append,Bool.or_eq_true,freeExactArgs bs name,freeExactArgs es name]
 termination_by sizeOf q
 theorem freeExactArgs (qs : Args) (name : Name) : name ∈ freeInventoryArgs qs ↔ freeOccursArgs name qs = true := by
  cases qs with
  | nil => simp [freeInventoryArgs,freeOccursArgs]
  | cons q qs => simp only [freeInventoryArgs,freeOccursArgs,List.mem_append,Bool.or_eq_true,freeExact q name,freeExactArgs qs name]
 termination_by sizeOf qs
end
mutual
 theorem containsLiteral (q : Expr) (ρ : Ty) (h : ρ ∈ support q) : ρ ∈ auxiliarySupport q := by
  cases q with
  | free σ x => exact h
  | bound σ i => exact h
  | lam σ q =>
    simp only [support,List.mem_append] at h
    simp only [auxiliarySupport,List.mem_append]
    rcases h with (h|h)|h
    · exact Or.inl (Or.inl h)
    · exact Or.inl (Or.inr h)
    · exact Or.inr (containsLiteral q ρ h)
  | head f bs =>
    simp only [support,List.mem_append] at h
    simp only [auxiliarySupport,declaration,List.mem_append]
    rcases h with h|h
    · exact Or.inl (Or.inl h)
    · exact Or.inr (containsLiteralArgs bs ρ h)
  | marked f τ bs es =>
    simp only [support,List.mem_append] at h
    simp only [auxiliarySupport,List.mem_append]
    rcases h with (h|h)|h
    · exact Or.inl (Or.inl (Or.inr h))
    · exact Or.inl (Or.inr (containsLiteralArgs bs ρ h))
    · exact Or.inr (containsLiteralArgs es ρ h)
 termination_by sizeOf q
 theorem containsLiteralArgs (qs : Args) (ρ : Ty) (h : ρ ∈ supportArgs qs) : ρ ∈ auxiliaryArgs qs := by
  cases qs with
  | nil => exact h
  | cons q qs =>
    simp only [supportArgs,List.mem_append] at h
    simp only [auxiliaryArgs,List.mem_append]
    exact h.elim (fun h => Or.inl (containsLiteral q ρ h)) (fun h => Or.inr (containsLiteralArgs qs ρ h))
 termination_by sizeOf qs
end
mutual
 theorem declarations (q : Expr) (f : Head) (hf : f ∈ heads q) (ρ : Ty) (hρ : ρ ∈ declaration f) : ρ ∈ auxiliarySupport q := by
  cases q with
  | free σ x => cases hf
  | bound σ i => cases hf
  | lam σ q => exact List.mem_append_right _ (declarations q f hf ρ hρ)
  | head g bs =>
    simp only [heads,List.mem_cons] at hf
    rcases hf with rfl|hf
    · exact List.mem_append_left _ hρ
    · exact List.mem_append_right _ (declarationsArgs bs f hf ρ hρ)
  | marked g τ bs es =>
    simp only [heads,List.mem_cons,List.mem_append] at hf
    simp only [auxiliarySupport,List.mem_append]
    rcases hf with rfl|(hf|hf)
    · exact Or.inl (Or.inl (Or.inl hρ))
    · exact Or.inl (Or.inr (declarationsArgs bs f hf ρ hρ))
    · exact Or.inr (declarationsArgs es f hf ρ hρ)
 termination_by sizeOf q
 theorem declarationsArgs (qs : Args) (f : Head) (hf : f ∈ headsArgs qs) (ρ : Ty) (hρ : ρ ∈ declaration f) : ρ ∈ auxiliaryArgs qs := by
  cases qs with
  | nil => cases hf
  | cons q qs =>
    simp only [headsArgs,List.mem_append] at hf
    simp only [auxiliaryArgs,List.mem_append]
    exact hf.elim (fun h => Or.inl (declarations q f h ρ hρ)) (fun h => Or.inr (declarationsArgs qs f h ρ hρ))
 termination_by sizeOf qs
end

theorem declaredBase (Γ : BoundContext) (bs : Args) (types : List Ty) (ht : BaseTyped Γ bs types)
    (ρ : Ty) (h : ρ ∈ types.flatMap subtypes) : ρ ∈ supportArgs bs := by
  cases bs with
  | nil => cases ht; simp at h
  | cons q qs =>
    cases ht with
    | cons hq hqs =>
      simp only [List.flatMap_cons,List.mem_append] at h
      simp only [supportArgs,List.mem_append]
      rcases h with h|h
      · exact Or.inl (TypeSupportFoundationProof.rootSupport q ρ (by simpa [SpineShiftProof.annotationExact Γ q _ hq] using h))
      · exact Or.inr (declaredBase Γ qs _ hqs ρ h)
termination_by sizeOf bs
mutual
 theorem ordinaryExact (Γ : BoundContext) (q : Expr) (τ : Ty) (ht : Typed Γ q τ) (ho : Ordinary q) (ρ : Ty) :
    ρ ∈ auxiliarySupport q ↔ ρ ∈ support q := by
  cases q with
  | free σ x => rfl
  | bound σ i => rfl
  | lam σ q =>
    cases ht with
    | lam hq => simp only [auxiliarySupport,support,List.mem_append,ordinaryExact (Γ.push σ) q _ hq ho ρ]
  | head f bs =>
    cases ht with
    | head hb =>
      simp only [auxiliarySupport,support,declaration,List.mem_append,ordinaryExactArgs Γ bs _ hb ho ρ]
      constructor
      · rintro ((h|h)|h)
        · exact Or.inl h
        · exact Or.inr (declaredBase Γ bs f.arguments hb ρ h)
        · exact Or.inr h
      · rintro (h|h)
        · exact Or.inl (Or.inl h)
        · exact Or.inr h
  | marked f τ bs es => exact False.elim ho
 termination_by sizeOf q
 theorem ordinaryExactArgs (Γ : BoundContext) (qs : Args) (types : List Ty) (ht : BaseTyped Γ qs types) (ho : OrdinaryArgs qs) (ρ : Ty) :
    ρ ∈ auxiliaryArgs qs ↔ ρ ∈ supportArgs qs := by
  cases qs with
  | nil => rfl
  | cons q qs =>
    cases ht with
    | cons hq hqs => simp only [auxiliaryArgs,supportArgs,List.mem_append,ordinaryExact Γ q _ hq ho.1 ρ,ordinaryExactArgs Γ qs _ hqs ho.2 ρ]
 termination_by sizeOf qs
end

theorem rankedDeclaration (name arity : Nat) (ρ : Ty) : ρ ∈ declaration (.ranked name arity) ↔ ρ = Ty.ground := by
  simp only [declaration,Head.result,Head.arguments,subtypes,List.mem_append,List.mem_singleton]
  constructor
  · rintro (h|h)
    · exact h
    · obtain ⟨σ,hσ,hρ⟩ := List.mem_flatMap.mp h
      have : σ = Ty.ground := (List.mem_replicate.mp hσ).2
      subst σ
      simpa [subtypes] using hρ
  · exact Or.inl

theorem subtypeTrans (σ τ ρ : Ty) (hτ : τ ∈ subtypes σ) (hρ : ρ ∈ subtypes τ) : ρ ∈ subtypes σ := by
  cases σ with
  | ground => simp only [subtypes,List.mem_singleton] at hτ; subst τ; exact hρ
  | arrow α β =>
    simp only [subtypes,List.mem_cons,List.mem_append] at hτ
    rcases hτ with rfl|(hτ|hτ)
    · exact hρ
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (subtypeTrans α τ ρ hτ hρ))
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (subtypeTrans β τ ρ hτ hρ))
termination_by sizeOf σ

def Closed (xs : List Ty) : Prop := ∀ σ, σ ∈ xs → ∀ ρ, ρ ∈ subtypes σ → ρ ∈ xs
 theorem subtypesClosed (τ : Ty) : Closed (subtypes τ) := fun σ hσ ρ hρ => subtypeTrans τ σ ρ hσ hρ
 theorem appendClosed (xs ys : List Ty) (hx : Closed xs) (hy : Closed ys) : Closed (xs ++ ys) := by
  intro σ hσ ρ hρ
  rcases List.mem_append.mp hσ with h|h
  · exact List.mem_append_left _ (hx σ h ρ hρ)
  · exact List.mem_append_right _ (hy σ h ρ hρ)
 theorem flatClosed (xs : List Ty) : Closed (xs.flatMap subtypes) := by
  intro σ hσ ρ hρ
  obtain ⟨τ,hτ,h⟩ := List.mem_flatMap.mp hσ
  exact List.mem_flatMap.mpr ⟨τ,hτ,subtypeTrans τ σ ρ h hρ⟩
 theorem declarationClosed (f : Head) : Closed (declaration f) := appendClosed _ _ (subtypesClosed _) (flatClosed _)
mutual
 theorem auxiliaryClosed (q : Expr) : Closed (auxiliarySupport q) := by
  cases q with
  | free σ x => exact subtypesClosed σ
  | bound σ i => exact subtypesClosed σ
  | lam σ q => exact appendClosed _ _ (appendClosed _ _ (subtypesClosed _) (subtypesClosed _)) (auxiliaryClosed q)
  | head f bs => exact appendClosed _ _ (declarationClosed f) (auxiliaryClosedArgs bs)
  | marked f τ bs es => exact appendClosed _ _ (appendClosed _ _ (appendClosed _ _ (declarationClosed f) (subtypesClosed τ)) (auxiliaryClosedArgs bs)) (auxiliaryClosedArgs es)
 termination_by sizeOf q
 theorem auxiliaryClosedArgs (qs : Args) : Closed (auxiliaryArgs qs) := by
  cases qs with
  | nil => intro σ h; cases h
  | cons q qs => exact appendClosed _ _ (auxiliaryClosed q) (auxiliaryClosedArgs qs)
 termination_by sizeOf qs
end
end LogicLineages.PersistentMarking.DecisionInventoryProof
