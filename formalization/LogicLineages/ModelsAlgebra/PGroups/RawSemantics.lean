module
public import LogicLineages.ModelsAlgebra.PGroups.RawSemanticsTargets
@[expose] public section
namespace LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
open GroupBackAndForth
universe u

theorem raw_term_agreement : Targets.groupRawTermAgreement.{u} := by
  intro G _ n a t
  induction t <;> simp_all [rawTermEval, GroupTerm.eval, RawGroupStructure.ofGroup]
  all_goals rfl

theorem raw_qf_agreement : Targets.groupRawQFAgreement.{u} := by
  intro G _ n a q
  induction q with
  | equal s t =>
    change rawTermEval (RawGroupStructure.ofGroup G) a s = rawTermEval (RawGroupStructure.ofGroup G) a t ↔ s.eval a = t.eval a
    rw [raw_term_agreement G n a s, raw_term_agreement G n a t]
  | falsum => rfl
  | neg q ih => exact not_congr ih
  | and q r ihq ihr => exact and_congr ihq ihr

theorem raw_formula_agreement : Targets.groupRawFormulaAgreement.{u} := by
  intro G _ n a φ
  induction φ with
  | qf q => exact raw_qf_agreement G _ a q
  | disjEx s m matrix ih =>
    simp only [Formula.RawRealize, Formula.Realize]
    exact exists_congr (fun i => exists_congr (fun c => ih i _))
  | conjAll s m matrix ih =>
    simp only [Formula.RawRealize, Formula.Realize]
    exact forall_congr' (fun i => forall_congr' (fun c => ih i _))

end LogicLineages.ModelsAlgebra.PGroups.GroupInfinitary
