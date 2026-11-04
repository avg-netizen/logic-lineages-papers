module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecisionTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnarySignProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecision.Proof
open SnyatkovUnarySign IntegerAlgorithms.Proof
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem atom_pr : Primrec₂ atomValue :=
  (Primrec.eq.comp
    (sign_primitive.comp (SnyatkovUnarySign.Proof.actualPrimitiveRecursion.1.comp
      (Primrec.fst.comp Primrec.fst) Primrec.snd))
    (Primrec.snd.comp Primrec.fst)).decide

private theorem clause_pr : Primrec₂ clauseValue := by
  have hp : PrimrecRel (fun a : Atom => fun n : Nat => atomValue a n = true) :=
    Primrec.eq.comp atom_pr (Primrec.const true)
  apply hp.forall_mem_list.decide.of_eq
  intro C n
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, clauseValue, List.all_eq_true]

private theorem matrix_pr : Primrec₂ matrixValue := by
  have hp : PrimrecRel (fun C : Clause => fun n : Nat => clauseValue C n = true) :=
    Primrec.eq.comp clause_pr (Primrec.const true)
  apply hp.exists_mem_list.decide.of_eq
  intro M n
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, matrixValue, List.any_eq_true]

private theorem tail_atom_pr : Primrec tailAtom :=
  (Primrec.eq.comp (SnyatkovUnarySign.Proof.actualPrimitiveRecursion.2.2.2.comp Primrec.fst)
    Primrec.snd).decide

private theorem tail_clause_pr : Primrec (fun C : Clause => C.all tailAtom) := by
  have hp : PrimrecPred (fun a : Atom => tailAtom a = true) :=
    Primrec.eq.comp tail_atom_pr (Primrec.const true)
  apply hp.forall_mem_list.decide.of_eq
  intro C
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.all_eq_true, id_eq]

private theorem tail_pr : Primrec tailValue := by
  have hp : PrimrecPred (fun C : Clause => C.all tailAtom = true) :=
    Primrec.eq.comp tail_clause_pr (Primrec.const true)
  apply hp.exists_mem_list.decide.of_eq
  intro M
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, tailValue, List.any_eq_true]

private theorem domain_pr : Primrec matrixDomain := by
  have hl : Primrec (fun M : Matrix => (M.flatten).map (fun a => domainBound a.1)) :=
    Primrec.list_map Primrec.list_flatten
      (SnyatkovUnarySign.Proof.actualPrimitiveRecursion.2.1.comp
        (Primrec.fst.comp Primrec.snd)).to₂
  exact Primrec.list_foldr hl (Primrec.const 0)
    (Primrec.nat_max.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂

private theorem threshold_sum_pr :
    Primrec (fun M : Matrix => ((M.flatten).map (fun a => threshold a.1)).sum) := by
  have hl : Primrec (fun M : Matrix => (M.flatten).map (fun a => threshold a.1)) :=
    Primrec.list_map Primrec.list_flatten
      (SnyatkovUnarySign.Proof.actualPrimitiveRecursion.2.2.1.comp
        (Primrec.fst.comp Primrec.snd)).to₂
  apply (Primrec.list_foldr hl (Primrec.const 0)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro M
  generalize (M.flatten).map (fun a => threshold a.1) = xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, List.sum_cons, ih]

private theorem threshold_pr : Primrec matrixThreshold :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp domain_pr (Primrec.const 1)) threshold_sum_pr

attribute [local irreducible] matrixValue tailValue matrixDomain matrixThreshold atomValue clauseValue

private theorem domain_check_pr :
    Primrec (fun p : Matrix × Nat => decide (matrixDomain p.1 ≤ p.2)) :=
  (Primrec.nat_le.comp (domain_pr.comp Primrec.fst) Primrec.snd).decide

private theorem exists_finite_pr : Primrec (fun M : Matrix =>
    (List.range (matrixThreshold M)).any (fun n =>
      decide (matrixDomain M ≤ n) && matrixValue M n)) := by
  have hp : PrimrecRel (fun n : Nat => fun M : Matrix =>
      (decide (matrixDomain M ≤ n) && matrixValue M n) = true) :=
    Primrec.eq.comp
      ((Primrec.and.comp domain_check_pr matrix_pr).comp (Primrec.pair Primrec.snd Primrec.fst))
      (Primrec.const true)
  apply ((hp.exists_mem_list.comp (Primrec.list_range.comp threshold_pr) Primrec.id).decide).of_eq
  intro M
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.any_eq_true, id_eq]
  rfl

private theorem forall_finite_pr : Primrec (fun M : Matrix =>
    (List.range (matrixThreshold M)).all (fun n =>
      (!decide (matrixDomain M ≤ n)) || matrixValue M n)) := by
  have hp : PrimrecRel (fun n : Nat => fun M : Matrix =>
      ((!decide (matrixDomain M ≤ n)) || matrixValue M n) = true) :=
    Primrec.eq.comp
      ((Primrec.or.comp (Primrec.not.comp domain_check_pr) matrix_pr).comp
        (Primrec.pair Primrec.snd Primrec.fst)) (Primrec.const true)
  apply ((hp.forall_mem_list.comp (Primrec.list_range.comp threshold_pr) Primrec.id).decide).of_eq
  intro M
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, List.all_eq_true, id_eq]
  rfl

theorem actualPrimitiveRecursion : Targets.ActualPrimitiveRecursion :=
  ⟨domain_pr, threshold_pr, matrix_pr, tail_pr,
    Primrec.or.comp exists_finite_pr tail_pr,
    Primrec.and.comp forall_finite_pr tail_pr⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovUnaryDecision.Proof
