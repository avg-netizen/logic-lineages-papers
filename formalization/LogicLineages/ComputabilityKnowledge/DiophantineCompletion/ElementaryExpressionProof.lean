module
public import LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementarySupportProof

@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryExpressionProof
open Elementary ElementaryTargets ElementarySupportProof

private theorem expr_self_mem {α : Type} [DecidableEq α] (e : Expr α) : e ∈ e.subterms := by
  cases e <;> simp [Expr.subterms]

private theorem subterms_nested {α : Type} [DecidableEq α] (e t : Expr α)
    (h : t ∈ e.subterms) : t.subterms ⊆ e.subterms := by
  induction e with
  | constant c =>
      simp only [Expr.subterms,Finset.mem_singleton] at h
      subst t
      exact Finset.Subset.refl _
  | «variable» i =>
      simp only [Expr.subterms,Finset.mem_singleton] at h
      subst t
      exact Finset.Subset.refl _
  | add p q ihp ihq =>
      simp only [Expr.subterms,Finset.mem_insert,Finset.mem_union] at h
      rcases h with rfl | hp | hq
      · exact Finset.Subset.refl _
      · intro u hu
        have h := ihp hp hu
        simp [Expr.subterms,h]
      · intro u hu
        have h := ihq hq hu
        simp [Expr.subterms,h]
  | mul p q ihp ihq =>
      simp only [Expr.subterms,Finset.mem_insert,Finset.mem_union] at h
      rcases h with rfl | hp | hq
      · exact Finset.Subset.refl _
      · intro u hu
        have h := ihp hp hu
        simp [Expr.subterms,h]
      · intro u hu
        have h := ihq hq hu
        simp [Expr.subterms,h]

private def nodeRHS {α : Type} [DecidableEq α] (s : Finset (Expr α))
    (closed : ∀ t ∈ s, t.subterms ⊆ s) : {t // t ∈ s} → RHS α {t // t ∈ s}
  | ⟨.constant c,_⟩ => .constant c
  | ⟨.variable i,_⟩ => .parameter i
  | ⟨.add p q,ht⟩ => .add
      ⟨p,closed _ ht (by simp [Expr.subterms,expr_self_mem])⟩
      ⟨q,closed _ ht (by simp [Expr.subterms,expr_self_mem])⟩
  | ⟨.mul p q,ht⟩ => .mul
      ⟨p,closed _ ht (by simp [Expr.subterms,expr_self_mem])⟩
      ⟨q,closed _ ht (by simp [Expr.subterms,expr_self_mem])⟩

private def nodeConstraint {α : Type} [DecidableEq α] (s : Finset (Expr α))
    (closed : ∀ t ∈ s, t.subterms ⊆ s) (t : {t // t ∈ s}) : Constraint α {t // t ∈ s} :=
  ⟨t,nodeRHS s closed t⟩

private theorem nodeCanonical {α : Type} [DecidableEq α] (s : Finset (Expr α))
    (closed : ∀ t ∈ s, t.subterms ⊆ s) (ν : α → Nat) (t : {t // t ∈ s}) :
    (nodeConstraint s closed t).Holds ν (fun e => e.val.eval ν) := by
  obtain ⟨t,ht⟩ := t
  cases t <;> rfl

private theorem nodeSound {α : Type} [DecidableEq α] (s : Finset (Expr α))
    (closed : ∀ t ∈ s, t.subterms ⊆ s) (ν : α → Nat) (w : {t // t ∈ s} → Nat)
    (h : ∀ t, (nodeConstraint s closed t).Holds ν w) :
    ∀ t (ht : t ∈ s), w ⟨t,ht⟩=t.eval ν := by
  intro t
  induction t with
  | constant c => intro ht; exact h ⟨.constant c,ht⟩
  | «variable» i => intro ht; exact h ⟨.variable i,ht⟩
  | add p q ihp ihq =>
      intro ht
      have hp : p ∈ s := closed _ ht (by simp [Expr.subterms,expr_self_mem])
      have hq : q ∈ s := closed _ ht (by simp [Expr.subterms,expr_self_mem])
      have he := h ⟨.add p q,ht⟩
      change w ⟨.add p q,ht⟩=w ⟨p,hp⟩+w ⟨q,hq⟩ at he
      rw [ihp hp,ihq hq] at he
      exact he
  | mul p q ihp ihq =>
      intro ht
      have hp : p ∈ s := closed _ ht (by simp [Expr.subterms,expr_self_mem])
      have hq : q ∈ s := closed _ ht (by simp [Expr.subterms,expr_self_mem])
      have he := h ⟨.mul p q,ht⟩
      change w ⟨.mul p q,ht⟩=w ⟨p,hp⟩*w ⟨q,hq⟩ at he
      rw [ihp hp,ihq hq] at he
      exact he

theorem expressionSystemNormalization : ExpressionSystemNormalization := by
  intro α p q
  classical
  let s := p.subterms ∪ q.subterms
  have hs : ∀ t ∈ s, t.subterms ⊆ s := by
    intro t ht u hu
    rcases Finset.mem_union.mp ht with ht | ht
    · exact Finset.mem_union.mpr (Or.inl (subterms_nested p t ht hu))
    · exact Finset.mem_union.mpr (Or.inr (subterms_nested q t ht hu))
  have hp : p ∈ s := Finset.mem_union.mpr (Or.inl (expr_self_mem p))
  have hq : q ∈ s := Finset.mem_union.mpr (Or.inr (expr_self_mem q))
  let β := {t // t ∈ s}
  letI : Fintype β := inferInstance
  let C : β ⊕ Unit → Constraint α β := fun j => match j with
    | .inl t => nodeConstraint s hs t
    | .inr _ => ⟨⟨p,hp⟩,.variable ⟨q,hq⟩⟩
  apply representsExt (finiteSystem C)
  intro ν
  constructor
  · rintro ⟨w,hw⟩
    have he := hw (.inr ())
    change w ⟨p,hp⟩=w ⟨q,hq⟩ at he
    have hn := nodeSound s hs ν w (fun t => hw (.inl t))
    rw [hn p hp,hn q hq] at he
    exact he
  · intro he
    refine ⟨fun t => t.val.eval ν,?_⟩
    intro j
    cases j with
    | inl t => exact nodeCanonical s hs ν t
    | inr u => exact he

end LogicLineages.ComputabilityKnowledge.DiophantineCompletion.ElementaryExpressionProof
