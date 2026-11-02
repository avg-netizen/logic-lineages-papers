module
public import LogicLineages.OrdinalComparison.UnitContextSelectionCodeTargets
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.UnitContextSelectionCode.Proof

theorem exactTypedSelection : Targets.ExactTypedSelection := by
  intro Γ
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    cases σ with
    | ground =>
      cases hs : UnitElimination.select Γ <;>
        simp only [hs,selectionCode,List.map_append,List.map_cons] at ih <;>
        simp [UnitElimination.select,hs,selectionCode,selectCode,SyntaxCode.typeCode,ih]
    | arrow a b => simp [UnitElimination.select,selectionCode,selectCode,SyntaxCode.typeCode,SyntaxCode.arrowCode]

private theorem none_iff (Γ : List Nat) : selectCode Γ=none ↔ ∀ σ ∈ Γ, σ=0 := by
  induction Γ with
  | nil => simp [selectCode]
  | cons σ Γ ih =>
    by_cases h : σ=0
    · subst σ; simp [selectCode,ih]
    · simp [selectCode,h]

private theorem split_sound (Γ left right : List Nat) (σ : Nat)
    (h : selectCode Γ=some (left,σ,right)) :
    Γ=left++σ::right ∧ (∀ τ ∈ left,τ=0) ∧ σ≠0 := by
  induction Γ generalizing left right σ with
  | nil => simp [selectCode] at h
  | cons x Γ ih =>
    by_cases hx : x=0
    · subst x
      change (selectCode Γ).map (fun r : Split => (0::r.1,r.2.1,r.2.2)) = some (left,σ,right) at h
      obtain ⟨⟨l,s,r⟩,hs,he⟩ := Option.map_eq_some_iff.mp h
      simp only [Prod.mk.injEq] at he
      rcases he with ⟨rfl,rfl,rfl⟩
      obtain ⟨hΓ,hl,hn⟩ := ih l r s hs
      exact ⟨by simp [hΓ],by simpa using hl,hn⟩
    · simp only [selectCode,if_neg hx,Option.some.injEq,Prod.mk.injEq] at h
      rcases h with ⟨rfl,rfl,rfl⟩
      exact ⟨rfl,by simp,hx⟩

private theorem split_complete (left right : List Nat) (σ : Nat)
    (hl : ∀ τ ∈ left,τ=0) (hs : σ≠0) : selectCode (left++σ::right)=some (left,σ,right) := by
  induction left with
  | nil => simp [selectCode,hs]
  | cons x left ih =>
    have hx := hl x (by simp)
    subst x
    have ht : ∀ τ ∈ left,τ=0 := fun τ hτ => hl τ (List.mem_cons_of_mem _ hτ)
    simp [selectCode,ih ht]

theorem exactRawSplit : Targets.ExactRawSplit := by
  refine ⟨none_iff,?_,?_⟩
  · intro Γ left right σ
    constructor
    · exact split_sound Γ left right σ
    · rintro ⟨rfl,hl,hs⟩
      exact split_complete left right σ hl hs
  · intro Γ left right σ h
    have he := (split_sound Γ left right σ h).1
    rw [he]
    simp

private def step (s : Nat×List Nat×Option Split) : Option Split :=
  if s.1=0 then s.2.2.map (fun r => (0::r.1,r.2.1,r.2.2)) else some ([],s.1,s.2.1)

private theorem step_primitive : Primrec step := by
  have hmap : Primrec (fun s : Nat×List Nat×Option Split => s.2.2.map (fun r => (0::r.1,r.2.1,r.2.2))) := by
    apply Primrec.option_map (Primrec.snd.comp Primrec.snd)
    exact ((Primrec.list_cons.comp (Primrec.const 0) (Primrec.fst.comp Primrec.snd)).pair
      ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
        (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))).to₂
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) hmap
    (Primrec.option_some.comp ((Primrec.const []).pair (Primrec.fst.pair (Primrec.fst.comp Primrec.snd))))

theorem primitiveRecursiveSelection : Targets.PrimitiveRecursiveSelection := by
  have h := Primrec.list_rec (Primrec.id (α := List Nat)) (Primrec.const (none : Option Split))
    (step_primitive.comp Primrec.snd).to₂
  apply h.of_eq
  intro Γ
  induction Γ with
  | nil => rfl
  | cons σ Γ ih =>
    change (List.rec none (fun b l IH => step (b,l,IH)) Γ) = selectCode Γ at ih
    change step (σ,Γ,List.rec none (fun b l IH => step (b,l,IH)) Γ) = selectCode (σ::Γ)
    rw [ih]
    rfl
end LogicLineages.OrdinalComparison.Source.UnitContextSelectionCode.Proof
