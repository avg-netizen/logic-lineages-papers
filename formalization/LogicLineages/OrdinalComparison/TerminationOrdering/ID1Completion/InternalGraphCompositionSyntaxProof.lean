module
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionTargets
public import LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalFiniteBlocksProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
open FirstOrder Language PositiveArithmeticOperators InternalCalculus InternalGraphComposition InternalFiniteBlocks
open InternalBinderTransportSyntaxProof InternalBinderTransportProof InternalTermSubstitutionSyntaxProof
open InternalTermSubstitutionProof InternalFiniteBlocksBindingProof InternalFiniteBlocksSubstitutionProof
open InternalSourceIntroductionSyntaxProof InternalSourceInversionSupportProof
open InternalTagArithmeticSyntaxProof (emb bindEmbedding varBind liftBind)

/-- Substitution commutes with the original finite bound prefix. -/
theorem bindSubst {L : Language} {α β : Type} (ts : α → L.Term β) {q k : Nat}
    (phi : L.BoundedFormula (α ⊕ Fin q) k) :
    (phi.relabel id).subst ts =
      (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)))).relabel id := by
  have ht (j : Nat) (t : L.Term ((α ⊕ Fin q) ⊕ Fin j)) :
      (t.relabel (BoundedFormula.relabelAux (id : α ⊕ Fin q → α ⊕ Fin q) j)).subst
        (Sum.elim (Term.relabel Sum.inl ∘ ts) (Term.var ∘ Sum.inr)) =
      (t.subst (Sum.elim
        (Term.relabel Sum.inl ∘ Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i : Fin q => .var (.inr i)))
        (Term.var ∘ Sum.inr))).relabel
          (BoundedFormula.relabelAux (id : β ⊕ Fin q → β ⊕ Fin q) j) := by
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

theorem exsSubst {L : Language} {α β : Type} {k : Nat} (phi : L.BoundedFormula α k) (ts : α → L.Term β) :
    phi.exs.subst ts = (phi.subst ts).exs := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change phi.ex.exs.subst ts = _
    rw [ih]
    rfl

theorem existsFinSubst {α β : Type} {k : Nat} (phi : OFormula (α ⊕ Fin k)) (ts : α → OTerm β) :
    (OrdinaryArithmetic.existsFin phi).subst ts = OrdinaryArithmetic.existsFin
      (phi.subst (Sum.elim (fun a => (ts a).relabel Sum.inl) (fun i => .var (.inr i)))) := by
  unfold OrdinaryArithmetic.existsFin
  rw [exsSubst,bindSubst]

theorem applyGraphSubst {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (out : OTerm α) (xs : Fin n → OTerm α) (ts : α → OTerm β) :
    (OrdinaryArithmetic.applyGraph f out xs).subst ts =
      OrdinaryArithmetic.applyGraph f (out.subst ts) (fun i => (xs i).subst ts) := by
  unfold OrdinaryArithmetic.applyGraph
  rw [formulaSubstComposition]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem andFinSubst {α β : Type} {n : Nat} (ps : Fin n → OFormula α) (ts : α → OTerm β) :
    (OrdinaryArithmetic.andFin ps).subst ts = OrdinaryArithmetic.andFin (fun i => (ps i).subst ts) := by
  have h (ls : List (OFormula α)) : (ls.foldr (· ⊓ ·) ⊤).subst ts =
      (ls.map (fun p => p.subst ts)).foldr (· ⊓ ·) ⊤ := by
    induction ls with
    | nil => rfl
    | cons p ps ih => change (p.subst ts ⊓ (ps.foldr (· ⊓ ·) ⊤).subst ts) = _; rw [ih]; rfl
  unfold OrdinaryArithmetic.andFin
  rw [h,List.map_ofFn]
  rfl

theorem embedSubst {α β : Type} (phi : OFormula α) (ts : α → OTerm β) :
    arithmeticEmbedding.onFormula (phi.subst ts) =
      (arithmeticEmbedding.onFormula phi).subst (fun a => emb (ts a)) :=
  onFormulaSubst arithmeticEmbedding phi ts

theorem graphSubst {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (out : OTerm α) (xs : Fin n → OTerm α) (ts : α → OTerm β) :
    (graph f out xs).subst (fun a => emb (ts a)) =
      graph f (out.subst ts) (fun i => (xs i).subst ts) := by
  unfold graph
  rw [← embedSubst,applyGraphSubst]

theorem graphExpanded {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (out : OTerm α) (xs : Fin n → OTerm α) :
    graph f out xs = (arithmeticEmbedding.onFormula f).subst (Fin.cases (emb out) (fun i => emb (xs i))) := by
  unfold graph OrdinaryArithmetic.applyGraph
  rw [embedSubst]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

theorem graphRename {α β : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (out : OTerm α) (xs : Fin n → OTerm α) (h : α → β) :
    (graph f out xs).relabel h = graph f (out.relabel h) (fun i => (xs i).relabel h) := by
  rw [graphExpanded,formulaSubstRelabel,graphExpanded]
  congr 1
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (onTermRelabel arithmeticEmbedding h out).symm
  · exact (onTermRelabel arithmeticEmbedding h (xs j)).symm

theorem graphOutputInstantiate {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (out : OTerm α) (xs : Fin n → OTerm α) :
    instantiate (graph f (.var (.inr (0 : Fin 1))) (fun i => (xs i).relabel Sum.inl)) (emb out) = graph f out xs := by
  rw [instantiate,bindEmbedding,graphSubst]
  simp only [varBind,liftBind]

theorem graphInstantiate {α : Type} {n : Nat} (f : OFormula (Fin (n+1)))
    (out : OTerm α) (xs : Fin n → OTerm α) (t : OTerm α) :
    instantiate (graph f (out.relabel Sum.inl) (fun i => (xs i).relabel Sum.inl)) (emb t) = graph f out xs := by
  rw [instantiate,bindEmbedding,graphSubst]
  simp only [liftBind]

theorem actualOriginalCompositionInstance : InternalGraphCompositionTargets.ActualOriginalCompositionInstance := by
  intro m n α f g out xs
  unfold graph OrdinaryArithmetic.applyGraph OrdinaryArithmetic.compositionGraph
  rw [existsFinSubst,actualOriginalBlockEmbedding]
  congr 1
  congr 1
  change ((OrdinaryArithmetic.applyGraph f (.var (Sum.inl (0 : Fin (m+1)) : Fin (m+1) ⊕ Fin n)) (fun i => .var (.inr i))).subst _ ⊓
    (OrdinaryArithmetic.andFin (fun i => OrdinaryArithmetic.applyGraph (g i) (.var (Sum.inr i : Fin (m+1) ⊕ Fin n))
      (fun j => .var (.inl j.succ)))).subst _) = _
  rw [applyGraphSubst,andFinSubst]
  simp only [applyGraphSubst,Term.subst,Sum.elim_inl,Sum.elim_inr,Fin.cases_zero,Fin.cases_succ]
  rfl

theorem matrixInstantiate {m n : Nat} {α : Type} (f : OFormula (Fin (n+1)))
    (g : Fin n → OFormula (Fin (m+1))) (out : OTerm α) (xs : Fin m → OTerm α)
    (ys : Fin n → OTerm α) :
    (arithmeticEmbedding.onFormula (matrix f g out xs)).subst (Sum.elim Term.var (fun i => emb (ys i))) =
      graph f out ys ⊓ arithmeticEmbedding.onFormula (OrdinaryArithmetic.andFin
        (fun i => OrdinaryArithmetic.applyGraph (g i) (ys i) xs)) := by
  have he : (Sum.elim Term.var (fun i => emb (ys i))) =
      (fun a => emb (Sum.elim Term.var ys a)) := by
    funext a
    cases a <;> rfl
  rw [he,← embedSubst]
  have ht (t : OTerm α) : (t.relabel Sum.inl).subst (Sum.elim Term.var ys) = t := by
    rw [termRelabelSubst]
    exact termSubstVar t
  unfold matrix
  change arithmeticEmbedding.onFormula ((OrdinaryArithmetic.applyGraph f _ _).subst _ ⊓
    (OrdinaryArithmetic.andFin _).subst _) = _
  rw [applyGraphSubst,andFinSubst]
  simp only [applyGraphSubst,ht,Term.subst,Sum.elim_inr]
  rfl
end LogicLineages.OrdinalComparison.TerminationOrdering.ID1Completion.InternalGraphCompositionSyntaxProof
