module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsTestProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsGraph
open FiniteSearchPrograms ScopedPhiProgramsGraph FiniteSearchProgramsProof
attribute [local irreducible] Nat.sqrt Nat.unpair BoundedSourcePrograms.Code.guard

abbrev Input := ScopedPhiProgramsGraph.Input

def assemble (p : Input) (results : List Bool) : Bool :=
  if ScopedPhiPrograms.Code.test [] p.2 then (ScopedPhiPrograms.Code.decide p.1 p.2).getD false
  else if p.2 % 5 = 0 ∨ p.2 % 5 = 1 then false
  else if p.2 % 5 = 2 then !results.getD 0 false
  else if p.2 % 5 = 3 then results.getD 0 false && results.getD 1 false
  else results.any id

theorem answer_equation (p : Input) :
    Code.answer p.1 p.2 = assemble p ((BoundedSourceProgramsGraph.children p).map (fun q => Code.answer q.1 q.2)) := by
  rw [Code.answer]
  by_cases hs : ScopedPhiPrograms.Code.test [] p.2 = true
  · simp [assemble, hs]
  by_cases hleaf : p.2 % 5 = 0 ∨ p.2 % 5 = 1
  · simp [assemble, hs, hleaf]
  by_cases h2 : p.2 % 5 = 2
  · simp [assemble, BoundedSourceProgramsGraph.children, hs, hleaf, h2]
  by_cases h3 : p.2 % 5 = 3
  · simp [assemble, BoundedSourceProgramsGraph.children, hs, hleaf, h2, h3]
  cases hg : BoundedSourcePrograms.Code.guard (p.2 / 5).unpair.1 (p.2 / 5).unpair.2 <;>
    simp [assemble, BoundedSourceProgramsGraph.children, BoundedSourceProgramsGraph.boundedChildren,
      hs, hleaf, h2, h3, hg, List.any_map, Function.comp_def]

theorem assemble_computable : Computable₂ assemble := by
  let A := Input × List Bool
  have h0 : Computable (fun p : A => p.2.getD 0 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 false) :=
    (Primrec.list_getD false).to_comp.comp Computable.snd (Computable.const 1)
  have hs : Computable (fun p : A => ScopedPhiPrograms.Code.test [] p.1.2) :=
    ScopedPhiProgramsProof.test_computable.comp (Computable.const []) (Computable.snd.comp Computable.fst)
  have hd : Computable (fun p : A => (ScopedPhiPrograms.Code.decide p.1.1 p.1.2).getD false) :=
    Computable.option_getD (ScopedPhiProgramsProof.decide_computable.comp (Computable.fst.comp Computable.fst)
      (Computable.snd.comp Computable.fst)) (Computable.const false)
  have hf : Computable (fun p : A =>
      if p.1.2 % 5 = 0 ∨ p.1.2 % 5 = 1 then false
      else if p.1.2 % 5 = 2 then !p.2.getD 0 false
      else if p.1.2 % 5 = 3 then p.2.getD 0 false && p.2.getD 1 false
      else p.2.any id) :=
    computable_ite (((tag_is 5 0).or (tag_is 5 1)).comp Primrec.fst).decide.to_comp (Computable.const false)
      (computable_ite ((tag_is 5 2).comp Primrec.fst).decide.to_comp (Primrec.not.to_comp.comp h0)
        (computable_ite ((tag_is 5 3).comp Primrec.fst).decide.to_comp (Primrec.and.to_comp.comp h0 h1)
          (BoundedSourceProgramsGraph.any_primitive.to_comp.comp Computable.snd)))
  apply (Computable.cond hs hd hf).of_eq
  intro p
  unfold assemble
  cases ScopedPhiPrograms.Code.test [] p.1.2 <;> rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsGraph
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsProof
open FiniteSearchPrograms FiniteSearchProgramsGraph

theorem answer_computable : Computable₂ Code.answer :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph Input Bool BoundedSourceProgramsGraph.children assemble Prod.snd
    BoundedSourceProgramsGraph.children_computable assemble_computable Computable.snd (fun p => Code.answer p.1 p.2)
    BoundedSourceProgramsGraph.children_decreasing answer_equation).2

theorem decide_computable : Computable₂ Code.decide := by
  apply (Computable.cond (test_computable.comp Computable.snd)
    (Computable.option_some.comp answer_computable) (Computable.const none)).of_eq
  intro p
  unfold Code.decide
  cases Code.test p.2 <;> rfl

theorem actualNumericPrograms : FiniteSearchProgramsTargets.ActualNumericPrograms :=
  ⟨test_computable, answer_computable, decide_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteSearchProgramsProof
