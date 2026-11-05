module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LeastSourceWitnessProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceGraph
open SourceWitnessTrace ScopedPhiProgramsGraph
attribute [local irreducible] Nat.sqrt Nat.unpair

abbrev Input := ScopedPhiProgramsGraph.Input
abbrev Output := Option (List Nat)

noncomputable def children (p : Input) : List Input :=
  if p.2 % 5 = 4 then
    (LeastSourceWitness.witness (p.1, (p.2 / 5).unpair.1, (p.2 / 5).unpair.2)).toList.map
      (fun n => (BoundedSourcePrograms.Code.update p.1 (p.2 / 5).unpair.1 n, (p.2 / 5).unpair.2))
  else []

noncomputable def assemble (p : Input) (results : List Output) : Output :=
  if FiniteSearchPrograms.Code.test p.2 then
    if p.2 % 5 = 4 then
      (LeastSourceWitness.witness (p.1, (p.2 / 5).unpair.1, (p.2 / 5).unpair.2)).bind
        (fun n => (results.getD 0 none).map (fun ns => n :: ns))
    else if FiniteSearchPrograms.Code.answer p.1 p.2 then some [] else none
  else none

theorem children_decreasing : ∀ p q, q ∈ children p → q.2 < p.2 := by
  intro p q h
  by_cases ht : p.2 % 5 = 4
  · have hp : 0 < p.2 := by omega
    have hd := Nat.div_lt_self hp (by decide : 1 < 5)
    have hr := Nat.unpair_right_le (p.2 / 5)
    cases hw : LeastSourceWitness.witness (p.1, (p.2 / 5).unpair.1, (p.2 / 5).unpair.2) with
    | none => simp [children, ht, hw] at h
    | some n =>
        simp [children, ht, hw] at h
        subst q
        exact lt_of_le_of_lt hr hd
  · simp [children, ht] at h

theorem equation (p : Input) : solve p.1 p.2 = assemble p ((children p).map (fun q => solve q.1 q.2)) := by
  rw [solve]
  by_cases hp : FiniteSearchPrograms.Code.test p.2 = true
  · by_cases ht : p.2 % 5 = 4
    · cases hw : LeastSourceWitness.witness (p.1, (p.2 / 5).unpair.1, (p.2 / 5).unpair.2) <;>
        simp [assemble, children, hp, ht, hw]
    · simp [assemble, hp, ht]
  · simp [assemble, hp]

theorem witness_computation : Computable (fun p : Input =>
    LeastSourceWitness.witness (p.1, (p.2 / 5).unpair.1, (p.2 / 5).unpair.2)) :=
  LeastSourceWitnessProof.witness_computable.comp
    (Computable.fst.pair ((left_primitive 5).to_comp.pair (right_primitive 5).to_comp))

theorem children_computable : Computable children := by
  have hs : Computable₂ (fun p : Input => fun n : Nat =>
      (BoundedSourcePrograms.Code.update p.1 (p.2 / 5).unpair.1 n, (p.2 / 5).unpair.2)) :=
    (BoundedSourceProgramsProof.update_primitive.to_comp.comp ((Computable.fst.comp Computable.fst).pair
      (((left_primitive 5).to_comp.comp Computable.fst).pair Computable.snd))).pair
      ((right_primitive 5).to_comp.comp Computable.fst)
  have hm := BoundedSourceProgramsProof.computable_map (Primrec.optionToList.to_comp.comp witness_computation) hs
  exact computable_ite (tag_is 5 4).decide.to_comp hm (Computable.const [])

theorem assemble_computable : Computable₂ assemble := by
  let A := Input × List Output
  have h0 : Computable (fun p : A => p.2.getD 0 none) :=
    (Primrec.list_getD none).to_comp.comp Computable.snd (Computable.const 0)
  have hw : Computable (fun p : A => LeastSourceWitness.witness (p.1.1, (p.1.2 / 5).unpair.1, (p.1.2 / 5).unpair.2)) :=
    witness_computation.comp Computable.fst
  have hm : Computable₂ (fun p : A => fun n : Nat => (p.2.getD 0 none).map (fun ns => n :: ns)) :=
    Computable.option_map (h0.comp Computable.fst)
      (Computable.list_cons.comp (Computable.snd.comp Computable.fst) Computable.snd).to₂
  have he := Computable.option_bind hw hm
  have ha : Computable (fun p : A => FiniteSearchPrograms.Code.answer p.1.1 p.1.2) :=
    FiniteSearchProgramsProof.answer_computable.comp (Computable.fst.comp Computable.fst) (Computable.snd.comp Computable.fst)
  have hl : Computable (fun p : A => if FiniteSearchPrograms.Code.answer p.1.1 p.1.2 then some [] else (none : Output)) := by
    apply (Computable.cond ha (Computable.const (some [])) (Computable.const none)).of_eq
    intro p; cases FiniteSearchPrograms.Code.answer p.1.1 p.1.2 <;> rfl
  have hf := computable_ite ((tag_is 5 4).comp Primrec.fst).decide.to_comp he hl
  have ht := FiniteSearchProgramsProof.test_computable.comp (Computable.snd.comp Computable.fst : Computable (fun p : A => p.1.2))
  apply (Computable.cond ht hf (Computable.const none)).of_eq
  intro p
  unfold assemble
  cases FiniteSearchPrograms.Code.test p.1.2 <;> rfl

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceGraph
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceProof
open SourceWitnessTrace SourceWitnessTraceGraph

theorem actualComputation : SourceWitnessTraceTargets.ActualComputation :=
  (BalancedBoxEvaluation.Graph.exactDecreasingGraph Input Output children assemble Prod.snd
    children_computable assemble_computable Computable.snd (fun p => solve p.1 p.2)
    children_decreasing equation).2

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceWitnessTraceProof
