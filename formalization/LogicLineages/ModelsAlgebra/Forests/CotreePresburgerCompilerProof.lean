module
public import LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompilerTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompiler.Proof
open FirstOrder Language CotreePresburgerLinear CotreePresburgerUnit

@[simp] theorem equality_realize {k : Nat} (s t : Affine k) (v : Fin k → Int) :
    CotreePresburgerDecision.Realize (equality s t) v ↔ s.eval v = t.eval v := by
  simp only [equality, CotreePresburgerDecision.Realize, Atom.eval,
    CotreePresburgerLinear.Proof.eval_add, CotreePresburgerLinear.Proof.eval_scale,
    neg_one_mul, decide_eq_true_eq]
  omega

theorem term_exact {α : Type} {n k : Nat} (t : presburger.Term (α ⊕ Fin n))
    (e : α ⊕ Fin n → Fin k) (v : Fin k → Nat) :
    (Affine.ofTerm (t.relabel e)).eval (fun i => (v i : Int)) =
      ((t.realize (fun a => v (e a)) : Nat) : Int) := by
  rw [CotreePresburgerLinear.StatementChecks.termTranslationExact, Term.realize_relabel]
  rfl

@[simp] theorem extend_free {α : Type} {n k : Nat} (e : α ⊕ Fin n → Fin k)
    (v : Fin k → Nat) (x : Nat) (a : α) :
    Fin.snoc (α := fun _ => Nat) v x (extend e (.inl a)) = v (e (.inl a)) := by
  simp [extend]

@[simp] theorem extend_bound {α : Type} {n k : Nat} (e : α ⊕ Fin n → Fin k)
    (v : Fin k → Nat) (x : Nat) :
    (fun i => Fin.snoc (α := fun _ => Nat) v x (extend e (.inr i))) =
      Fin.snoc (fun i => v (e (.inr i))) x := by
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i <;> simp [extend]

theorem compilationExact : Targets.CompilationExact := by
  classical
  intro α n k p
  induction p generalizing k with
  | falsum => intro e v; rfl
  | equal s t =>
    intro e v
    rw [compile, equality_realize, term_exact, term_exact]
    change ((s.realize (fun a => v (e a)) : Nat) : Int) =
        ((t.realize (fun a => v (e a)) : Nat) : Int) ↔ _
    rw [Int.natCast_inj]
    have he : (fun a => v (e a)) = Sum.elim (fun a => v (e (.inl a)))
        (fun i => v (e (.inr i))) := by
      funext a
      cases a <;> rfl
    simp only [he, BoundedFormula.Realize]
  | rel r ts => exact Empty.elim r
  | imp p q ihp ihq =>
    intro e v
    simp only [compile, CotreePresburgerDecision.Realize, ihp, ihq,
      BoundedFormula.Realize]
    tauto
  | all p ih =>
    intro e v
    simp only [compile, CotreePresburgerDecision.Realize, not_exists, not_not,
      BoundedFormula.Realize]
    apply forall_congr'
    intro x
    rw [← CotreePresburgerDecision.Proof.cast_snoc, ih]
    simp only [extend_free, extend_bound]

theorem formulaExact : Targets.FormulaExact := by
  intro n p v
  have h := compilationExact (Fin n) 0 n p (Sum.elim id Fin.elim0) v
  exact h.trans (Iff.of_eq (congrArg
    (fun w : Fin 0 → Nat => BoundedFormula.Realize p v w) (Subsingleton.elim _ _)))

theorem evaluationExact : Targets.EvaluationExact := by
  intro n p v
  rw [evaluate, CotreePresburgerDecision.StatementChecks.evaluationExact, formulaExact]

theorem satisfiabilityExact : Targets.SatisfiabilityExact := by
  intro n p
  rw [satisfiable, CotreePresburgerDecision.StatementChecks.satisfiabilityExact]
  exact exists_congr (fun v => formulaExact n p v)
end LogicLineages.ModelsAlgebra.Forests.CotreePresburgerCompiler.Proof
