module
public import LogicLineages.StandardControlCurrent.HFreeGraphNormalizationMatrixProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeProgramsProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NonlinearProjectionCompletion
open HFreeGraphNormalization
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair
abbrev PredicateCall := Nat × Nat

def predicateChildren (p : PredicateCall) : List PredicateCall :=
  if p.2 % 8 < 5 then [] else if p.2 % 8 = 5 then [(p.1,p.2 / 8)]
  else [(p.1,(p.2 / 8).unpair.1),
    (p.1 + ExpandedGraphCode.nodeCount (Code.forest (p.2 / 8).unpair.1),(p.2 / 8).unpair.2)]

def predicateAssemble (p : PredicateCall) (values : List Nat) : Nat :=
  if p.2 % 8 = 0 then 0 else if p.2 % 8 = 1 then 1
  else if p.2 % 8 = 2 ∨ p.2 % 8 = 3 then
    SourceRows.Code.relation (decide (p.2 % 8 = 3))
      (ExpandedGraphCode.output p.1 (p.2 / 8).unpair.1)
      (ExpandedGraphCode.output (p.1 + ExpandedGraphCode.nodeCount (p.2 / 8).unpair.1) (p.2 / 8).unpair.2)
  else if p.2 % 8 = 4 then
    let m := (p.2 / 8).unpair.1
    let z := ExpandedGraphCode.output p.1 (p.2 / 8).unpair.2
    let row : NormalForm.Code.RowData := (0,[(1,SourceTermGraph.Code.variableData z)])
    if m = 0 then SourceTermGraph.Code.equation row
    else 6 * Encodable.encode ((1,m-1,row) : NormalForm.Code.AtomData) + 2
  else if p.2 % 8 = 5 then 6 * values.getD 0 0 + 3
  else 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + (p.2 % 8 - 2)

theorem predicateChildren_computable : Computable predicateChildren := by
  have hl : Primrec (fun p : PredicateCall => (p.2 / 8).unpair.1) := matrixLeft_primitive.comp Primrec.snd
  have hr : Primrec (fun p : PredicateCall => (p.2 / 8).unpair.2) := matrixRight_primitive.comp Primrec.snd
  have hs : Computable (fun p : PredicateCall => p.1 + ExpandedGraphCode.nodeCount (Code.forest (p.2 / 8).unpair.1)) :=
    Primrec.nat_add.to_comp.comp Computable.fst
      (ExpandedGraphCodeProof.nodeCount_computable.comp (forest_computable.comp hl.to_comp))
  exact computable_ite ((Primrec.nat_lt.comp matrixTag_primitive (Primrec.const 5)).comp Primrec.snd)
    (Computable.const [])
    (computable_ite ((matrixTag_is 5).comp Primrec.snd)
      (Computable.list_cons.comp (Computable.fst.pair (matrixQuotient_primitive.to_comp.comp Computable.snd)) (Computable.const []))
      (Computable.list_cons.comp (Computable.fst.pair hl.to_comp)
        (Computable.list_cons.comp (hs.pair hr.to_comp) (Computable.const []))))

theorem predicateChildren_decreasing : ∀ p q : PredicateCall,
    q ∈ predicateChildren p → q.2 < p.2 := by
  intro p q h
  by_cases hleaf : p.2 % 8 < 5
  · simp [predicateChildren, hleaf] at h
  have hp : 0 < p.2 := by omega
  have hd := Nat.div_lt_self hp (show 1 < 8 by decide)
  have hl := Nat.unpair_left_le (p.2 / 8)
  have hr := Nat.unpair_right_le (p.2 / 8)
  unfold predicateChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false]
  all_goals rcases h with rfl | rfl <;> simp_all <;> omega

theorem predicate_equation (p : PredicateCall) :
    Code.predicate p.1 p.2 = predicateAssemble p
      ((predicateChildren p).map (fun q => Code.predicate q.1 q.2)) := by
  have hm : p.2 % 8 < 8 := Nat.mod_lt _ (by decide)
  rw [Code.predicate]
  unfold predicateAssemble predicateChildren
  split_ifs <;> simp_all <;> omega

theorem predicateAssemble_computable : Computable₂ predicateAssemble := by
  let C := PredicateCall × List Nat
  have hs : Computable (fun p : C => p.1.1) := Computable.fst.comp Computable.fst
  have hc : Primrec (fun p : C => p.1.2) := Primrec.snd.comp Primrec.fst
  have hl : Primrec (fun p : C => (p.1.2 / 8).unpair.1) := matrixLeft_primitive.comp hc
  have hr : Primrec (fun p : C => (p.1.2 / 8).unpair.2) := matrixRight_primitive.comp hc
  have h0 : Computable (fun p : C => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : C => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd (Computable.const 1)
  have hn := Primrec.nat_add.to_comp.comp hs (ExpandedGraphCodeProof.nodeCount_computable.comp hl.to_comp)
  have hol := ExpandedGraphCodeProof.output_computable.comp hs hl.to_comp
  have hor := ExpandedGraphCodeProof.output_computable.comp hn hr.to_comp
  have hz := ExpandedGraphCodeProof.output_computable.comp hs hr.to_comp
  have hrow : Computable (fun p : C => ((0 : Int), [(1,SourceTermGraph.Code.variableData
      (ExpandedGraphCode.output p.1.1 (p.1.2 / 8).unpair.2))] : NormalForm.Code.RowData)) :=
    (Computable.const (0 : Int)).pair (Computable.list_cons.comp
      ((Computable.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.to_comp.comp hz)) (Computable.const []))
  have hrel := SourceRowsCodeProof.relation_primitive.to_comp.comp
    (((matrixTag_is 3).comp hc).decide.to_comp.pair (hol.pair hor))
  have hdiv : Computable (fun p : C =>
      if (p.1.2 / 8).unpair.1 = 0 then SourceTermGraph.Code.equation
        (0,[(1,SourceTermGraph.Code.variableData (ExpandedGraphCode.output p.1.1 (p.1.2 / 8).unpair.2))])
      else 6 * Encodable.encode ((1,(p.1.2 / 8).unpair.1-1,
        (0,[(1,SourceTermGraph.Code.variableData (ExpandedGraphCode.output p.1.1 (p.1.2 / 8).unpair.2))])) : NormalForm.Code.AtomData) + 2) :=
    computable_ite (Primrec.eq.comp hl (Primrec.const 0))
      (SourceTermGraphCodeProof.equation_primitive.to_comp.comp hrow)
      (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 6)
        (Computable.encode.comp ((Computable.const 1).pair
          ((Primrec.nat_sub.to_comp.comp hl.to_comp (Computable.const 1)).pair hrow)))) (Computable.const 2))
  exact computable_ite ((matrixTag_is 0).comp hc) (Computable.const 0)
    (computable_ite ((matrixTag_is 1).comp hc) (Computable.const 1)
      (computable_ite (((matrixTag_is 2).or (matrixTag_is 3)).comp hc) hrel
        (computable_ite ((matrixTag_is 4).comp hc) hdiv
          (computable_ite ((matrixTag_is 5).comp hc)
            (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 6) h0) (Computable.const 3))
            (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 6)
              (Primrec₂.natPair.to_comp.comp h0 h1))
              (Primrec.nat_sub.to_comp.comp (matrixTag_primitive.to_comp.comp hc.to_comp) (Computable.const 2)))))))

theorem predicate_computable : Computable₂ Code.predicate := by
  classical
  exact (LayeredComparison.FiniteGraph.Proof.exactDecreasingGraph PredicateCall Nat predicateChildren predicateAssemble
    Prod.snd predicateChildren_computable predicateAssemble_computable Computable.snd
    (fun p => Code.predicate p.1 p.2) predicateChildren_decreasing predicate_equation).2
end LogicLineages.StandardControlCurrent.HFreeGraphNormalizationProof
