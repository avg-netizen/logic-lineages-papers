module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsChildrenProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsGraph
open BoundedSourcePrograms ScopedPhiProgramsGraph BoundedSourceProgramsProof
attribute [local irreducible] Nat.sqrt Nat.unpair Code.guard

def assemble (p : Input) (results : List Bool) : Bool :=
  if p.2 % 5 = 0 then decide (ScopedPhiPrograms.Code.value p.1 (p.2 / 5).unpair.1 = ScopedPhiPrograms.Code.value p.1 (p.2 / 5).unpair.2)
  else if p.2 % 5 = 1 then decide (ScopedPhiPrograms.Code.value p.1 (p.2 / 5).unpair.1 < ScopedPhiPrograms.Code.value p.1 (p.2 / 5).unpair.2)
  else if p.2 % 5 = 2 then !results.getD 0 false
  else if p.2 % 5 = 3 then results.getD 0 false && results.getD 1 false
  else results.any id

theorem answer_equation (p : Input) :
    Code.answer p.1 p.2 = assemble p ((children p).map (fun q => Code.answer q.1 q.2)) := by
  rw [Code.answer]
  by_cases h0 : p.2 % 5 = 0
  · simp [assemble, children, h0]
  by_cases h1 : p.2 % 5 = 1
  · simp [assemble, children, h0, h1]
  by_cases h2 : p.2 % 5 = 2
  · simp [assemble, children, h0, h1, h2]
  by_cases h3 : p.2 % 5 = 3
  · simp [assemble, children, h0, h1, h2, h3]
  cases hg : Code.guard (p.2 / 5).unpair.1 (p.2 / 5).unpair.2 <;>
    simp [assemble, children, boundedChildren, h0, h1, h2, h3, hg, List.any_map, Function.comp_def]

theorem any_primitive : Primrec (fun xs : List Bool => xs.any id) := by
  have hs : Primrec₂ (fun (_ : List Bool) (p : Bool × Bool) => p.1 || p.2) :=
    Primrec.or.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Bool => xs.foldr (fun b s => b || s) false) :=
    Primrec.list_foldr Primrec.id (Primrec.const false) hs
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr_cons, List.any_cons, ih, id_eq]

theorem assemble_computable : Computable₂ assemble := by
  let A := Input × List Bool
  have h0 : Computable (fun p : A => p.2.getD 0 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 1)
  have hl : Computable (fun p : A => ScopedPhiPrograms.Code.value p.1.1 (p.1.2 / 5).unpair.1) :=
    ScopedPhiProgramsProof.value_computable.comp (Computable.fst.comp Computable.fst) ((left_primitive 5).to_comp.comp Computable.fst)
  have hr : Computable (fun p : A => ScopedPhiPrograms.Code.value p.1.1 (p.1.2 / 5).unpair.2) :=
    ScopedPhiProgramsProof.value_computable.comp (Computable.fst.comp Computable.fst) ((right_primitive 5).to_comp.comp Computable.fst)
  have he := (show PrimrecRel (fun a b : Nat => a = b) from Primrec.eq).decide.to_comp.comp hl hr
  have hlt := Primrec.nat_lt.decide.to_comp.comp hl hr
  exact computable_ite ((tag_is 5 0).comp Primrec.fst).decide.to_comp he
    (computable_ite ((tag_is 5 1).comp Primrec.fst).decide.to_comp hlt
      (computable_ite ((tag_is 5 2).comp Primrec.fst).decide.to_comp (Primrec.not.to_comp.comp h0)
        (computable_ite ((tag_is 5 3).comp Primrec.fst).decide.to_comp (Primrec.and.to_comp.comp h0 h1)
          (any_primitive.to_comp.comp Computable.snd))))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsGraph
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsProof
open BoundedSourcePrograms BoundedSourceProgramsGraph

theorem answer_computable : Computable₂ Code.answer :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph Input Bool children assemble Prod.snd
    children_computable assemble_computable Computable.snd (fun p => Code.answer p.1 p.2)
    children_decreasing answer_equation).2

theorem decide_computable : Computable₂ Code.decide := by
  apply (Computable.cond (test_computable.comp Computable.snd)
    (Computable.option_some.comp answer_computable) (Computable.const none)).of_eq
  intro p
  unfold Code.decide
  cases Code.test p.2 <;> rfl

theorem actualNumericPrograms : BoundedSourceProgramsTargets.ActualNumericPrograms :=
  ⟨update_primitive, guard_computable, test_computable, answer_computable, decide_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedSourceProgramsProof
