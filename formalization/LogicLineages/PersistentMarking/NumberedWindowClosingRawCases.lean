import LogicLineages.PersistentMarking.NumberedWindowClosingBetaProof

namespace LogicLineages.PersistentMarking.NumberedWindowClosingRawCases
open NumberedWindowSyntax NumberedWindowClosing NumberedWindowRules
open NumberedWindowClosingOperationsProof
open NumberedWindowClosingInventoryProof (annotation)
open NameBridge (Name)

private theorem decrease (n : Name) {q r} (h : MarkDecrease q r) :
    ∀ d, MarkDecrease (closeAt n d q) (closeAt n d r) := by
  induction h with
  | omega => intro d; exact .omega
  | finite h => intro d; exact .finite h
  | lam _ ih => intro d; exact .lam (ih (d+1))

theorem replacement (n : Name) (d : Nat) {bs target}
    (h : PrimitiveReplacement bs target) :
    PrimitiveReplacement (closeArgsAt n d bs) (closeArgsAt n d target) := by
  obtain ⟨kept,removed,added,hSrc,hTgt,hNot,hOrigin⟩ := h
  let op := closeAt n d
  refine ⟨kept.map op,removed.map op,added.map op,?_,?_,?_,?_⟩
  · simpa only [asList,List.map_append,op] using hSrc.map op
  · simpa only [asList,List.map_append,op] using hTgt.map op
  · intro h
    exact hNot (List.map_eq_nil_iff.mp h)
  · intro a ha
    obtain ⟨a',ha',e⟩ := List.mem_map.mp ha
    subst a
    obtain ⟨q,hq,hm⟩ := hOrigin a' ha'
    exact ⟨op q,List.mem_map.mpr ⟨q,hq,rfl⟩,decrease n hm d⟩

theorem selection (n : Name) (d : Nat) {S K f τ k bs es i q ds r}
    (hg : bs.get i = some q ∨ es.get i = some q)
    (ht : q.type = Spine.ArrowPrefix ds τ)
    (ha : applications q (ownerCopies f k bs es ds) = some r) :
    RawStep S K (closeAt n d (.numbered f τ (k+1) bs es)) (closeAt n d r) := by
  have hg' : (closeArgsAt n d bs).get i = some (closeAt n d q) ∨
      (closeArgsAt n d es).get i = some (closeAt n d q) := by
    simp only [atIndex]
    exact hg.elim (fun h => Or.inl (by simp only [h,Option.map_some]))
      (fun h => Or.inr (by simp only [h,Option.map_some]))
  have ha' : applications (closeAt n d q)
      (ownerCopies f k (closeArgsAt n d bs) (closeArgsAt n d es) ds) = some (closeAt n d r) := by
    simp only [← copies n d,applyArgs,ha,Option.map_some]
  exact .select hg' ((annotation n d q).trans ht) ha'

theorem beta (n : Name) (d : Nat) {S K σ τ body a} :
    RawStep S K (closeAt n d (.auxApp σ τ (.lam σ body) a))
      (closeAt n d (substitute (.cons a .nil) 0 body)) := by
  have e := NumberedWindowClosingBetaProof.term n d 0 body a
  simp only [Nat.add_zero] at e
  rw [e]
  exact .beta

private theorem nonbottom (n : Name) (d : Nat) (q : NTerm)
    (h : q ≠ .bottom q.type) : closeAt n d q ≠ .bottom (closeAt n d q).type := by
  cases q with
  | free σ x =>
    unfold closeAt
    split <;> intro e <;> cases e
  | bound σ i => intro e; cases e
  | lam σ q => intro e; cases e
  | bottom σ => exact (h rfl).elim
  | ordinary f bs => intro e; cases e
  | numbered f τ k bs es => intro e; cases e
  | auxApp σ τ q a => intro e; cases e

theorem toBottom (n : Name) (d : Nat) {S K q} (h : q ≠ .bottom q.type) :
    RawStep S K (closeAt n d q) (closeAt n d (.bottom q.type)) := by
  rw [show closeAt n d (.bottom q.type) = .bottom (closeAt n d q).type by
    simp only [closeAt,annotation]]
  exact .bottom (nonbottom n d q h)

end LogicLineages.PersistentMarking.NumberedWindowClosingRawCases
