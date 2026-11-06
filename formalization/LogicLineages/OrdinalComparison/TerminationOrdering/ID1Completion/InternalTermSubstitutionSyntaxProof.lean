module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalBinderTransportProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionSyntaxProof
open FirstOrder Language InternalBinderTransportSyntaxProof

theorem termSubstRelabel {L : Language} {α β γ : Type} (t : L.Term α)
    (ts : α → L.Term β) (f : β → γ) :
    (t.subst ts).relabel f = t.subst (fun a => (ts a).relabel f) := by
  induction t with
  | var => rfl
  | func g xs ih => simp only [Term.subst,Term.relabel]; congr 1; funext i; exact ih i

theorem termSubstComposition {L : Language} {α β γ : Type} (t : L.Term α)
    (ts : α → L.Term β) (us : β → L.Term γ) :
    (t.subst ts).subst us = t.subst (fun a => (ts a).subst us) := by
  induction t with
  | var => rfl
  | func g xs ih => simp only [Term.subst]; congr 1; funext i; exact ih i

theorem formulaSubstComposition {L : Language} {α β γ : Type} {k : Nat}
    (phi : L.BoundedFormula α k) (ts : α → L.Term β) (us : β → L.Term γ) :
    (phi.subst ts).subst us = phi.subst (fun a => (ts a).subst us) := by
  have ht (j : Nat) (t : L.Term (α ⊕ Fin j)) :
      (t.subst (Sum.elim (Term.relabel Sum.inl ∘ ts) (Term.var ∘ Sum.inr))).subst
        (Sum.elim (Term.relabel Sum.inl ∘ us) (Term.var ∘ Sum.inr)) =
      t.subst (Sum.elim (fun a => ((ts a).subst us).relabel Sum.inl) (Term.var ∘ Sum.inr)) := by
    rw [termSubstComposition]
    congr 1
    funext i
    cases i with
    | inl a =>
      change ((ts a).relabel Sum.inl).subst _ = ((ts a).subst us).relabel Sum.inl
      rw [termRelabelSubst,termSubstRelabel]
      rfl
    | inr i => rfl
  induction phi with
  | falsum => rfl
  | equal t u => simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,ht]; rfl
  | rel r xs => simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,ht]; rfl
  | imp p q ihp ihq => exact congrArg₂ BoundedFormula.imp ihp ihq
  | all p ih => exact congrArg BoundedFormula.all ih

theorem substCast {L : Language} {α β : Type} (ts : α → L.Term β) {k l : Nat}
    (h : k ≤ l) (phi : L.BoundedFormula α k) :
    (phi.castLE h).subst ts = (phi.subst ts).castLE h := by
  have ht {j m : Nat} (h : j ≤ m) (t : L.Term (α ⊕ Fin j)) :
      (t.relabel (Sum.map id (Fin.castLE h))).subst
        (Sum.elim (Term.relabel Sum.inl ∘ ts) (Term.var ∘ Sum.inr)) =
      (t.subst (Sum.elim (Term.relabel Sum.inl ∘ ts) (Term.var ∘ Sum.inr))).relabel
        (Sum.map id (Fin.castLE h)) := by
    rw [termRelabelSubst,termSubstRelabel]
    congr 1
    funext i
    cases i with
    | inl a =>
      change (ts a).relabel Sum.inl = ((ts a).relabel Sum.inl).relabel _
      rw [Term.relabel_relabel]
      rfl
    | inr i => rfl
  induction phi generalizing l with
  | falsum => rfl
  | equal t u => simp only [BoundedFormula.castLE,BoundedFormula.subst,BoundedFormula.mapTermRel,ht]
  | rel r xs => simp only [BoundedFormula.castLE,BoundedFormula.subst,BoundedFormula.mapTermRel,
      Function.comp_apply,ht]; rfl
  | imp p q ihp ihq => exact congrArg₂ BoundedFormula.imp (ihp h) (ihq h)
  | all p ih => exact congrArg BoundedFormula.all (ih _)

theorem substBind {L : Language} {α β : Type} (ts : α → L.Term β) {k : Nat}
    (phi : L.BoundedFormula (α ⊕ Fin 1) k) :
    (phi.relabel id).subst ts =
      (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)))).relabel id := by
  have ht (j : Nat) (t : L.Term ((α ⊕ Fin 1) ⊕ Fin j)) :
      (t.relabel (BoundedFormula.relabelAux (id : α ⊕ Fin 1 → α ⊕ Fin 1) j)).subst
        (Sum.elim (Term.relabel Sum.inl ∘ ts) (Term.var ∘ Sum.inr)) =
      (t.subst (Sum.elim
        (Term.relabel Sum.inl ∘ Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i : Fin 1 => .var (.inr i)))
        (Term.var ∘ Sum.inr))).relabel
          (BoundedFormula.relabelAux (id : β ⊕ Fin 1 → β ⊕ Fin 1) j) := by
    rw [termRelabelSubst,termSubstRelabel]
    congr 1
    funext i
    rcases i with (a | x) | y
    · change (ts a).relabel Sum.inl = (((ts a).relabel Sum.inl).relabel Sum.inl).relabel _
      rw [Term.relabel_relabel,Term.relabel_relabel]
      congr 1
    · rfl
    · rfl
  induction phi with
  | falsum => rfl
  | equal t u => simp only [BoundedFormula.subst,BoundedFormula.relabel,BoundedFormula.mapTermRel,ht]
  | rel r xs => simp only [BoundedFormula.subst,BoundedFormula.relabel,BoundedFormula.mapTermRel,ht]
  | imp p q ihp ihq => exact congrArg₂ BoundedFormula.imp ihp ihq
  | all p ih =>
    change (((p.relabel id).castLE _).subst ts).all = _
    rw [substCast,ih]
    rfl

theorem onTermSubst {L L' : Language} (h : L →ᴸ L') {α β : Type}
    (t : L.Term α) (ts : α → L.Term β) :
    h.onTerm (t.subst ts) = (h.onTerm t).subst (fun a => h.onTerm (ts a)) := by
  induction t with
  | var => rfl
  | func g xs ih => simp only [Term.subst,LHom.onTerm]; congr 1; funext i; exact ih i

theorem onFormulaSubst {L L' : Language} (h : L →ᴸ L') {α β : Type} {k : Nat}
    (phi : L.BoundedFormula α k) (ts : α → L.Term β) :
    h.onBoundedFormula (phi.subst ts) = (h.onBoundedFormula phi).subst (fun a => h.onTerm (ts a)) := by
  have ht (j : Nat) (t : L.Term (α ⊕ Fin j)) :
      h.onTerm (t.subst (Sum.elim (Term.relabel Sum.inl ∘ ts) (Term.var ∘ Sum.inr))) =
      (h.onTerm t).subst (Sum.elim (fun a => (h.onTerm (ts a)).relabel Sum.inl) (Term.var ∘ Sum.inr)) := by
    rw [onTermSubst]
    congr 1
    funext i
    cases i with
    | inl a => exact onTermRelabel h Sum.inl (ts a)
    | inr i => rfl
  induction phi with
  | falsum => rfl
  | equal t u => simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,LHom.onBoundedFormula,
      Term.bdEqual,ht]; rfl
  | rel r xs =>
    simp only [BoundedFormula.subst,BoundedFormula.mapTermRel,LHom.onBoundedFormula,Relations.boundedFormula]
    congr 1
    funext i
    exact ht _ (xs i)
  | imp p q ihp ihq => exact congrArg₂ BoundedFormula.imp ihp ihq
  | all p ih => exact congrArg BoundedFormula.all ih

end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalTermSubstitutionSyntaxProof
