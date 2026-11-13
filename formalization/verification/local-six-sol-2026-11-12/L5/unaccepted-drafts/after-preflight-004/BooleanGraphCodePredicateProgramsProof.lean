module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeStructureProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeProof
open BooleanGraphCode NonlinearProjectionCompletion
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair
abbrev PredicateCall := Nat × Nat

def predicateChildren (p : PredicateCall) : List PredicateCall :=
  if p.2 % 8 = 0 ∨ p.2 % 8 = 1 ∨ p.2 % 8 = 2 ∨ p.2 % 8 = 3 ∨ p.2 % 8 = 4 then []
  else if p.2 % 8 = 5 then [(p.1, p.2 / 8)]
  else [(p.1, (p.2 / 8).unpair.1),
    (p.1 + ExpandedGraphCode.nodeCount (forest (p.2 / 8).unpair.1), (p.2 / 8).unpair.2)]

def predicateAssemble (p : PredicateCall) (values : List Nat) : Nat :=
  if p.2 % 8 = 0 then 0 else if p.2 % 8 = 1 then 1
  else if p.2 % 8 = 2 ∨ p.2 % 8 = 3 then
    SourceRows.Code.relation (p.2 % 8 == 3)
      (ExpandedGraphCode.output p.1 (p.2 / 8).unpair.1)
      (ExpandedGraphCode.output
        (p.1 + ExpandedGraphCode.nodeCount (p.2 / 8).unpair.1) (p.2 / 8).unpair.2)
  else if p.2 % 8 = 4 then
    let m := (p.2 / 8).unpair.1
    let x := ExpandedGraphCode.output p.1 (p.2 / 8).unpair.2
    if m = 0 then SourceTermGraph.Code.equation (0, [(1, SourceTermGraph.Code.variableData x)])
    else 6 * Encodable.encode ((1, m - 1, (0 : Int), [(1 : Int, SourceTermGraph.Code.variableData x)]) : NormalForm.Code.AtomData) + 2
  else if p.2 % 8 = 5 then 6 * values.getD 0 0 + 3
  else 6 * Nat.pair (values.getD 0 0) (values.getD 1 0) + (p.2 % 8 - 2)

theorem predicateChildren_computable : Computable predicateChildren := by
  have hs : Computable (fun p : PredicateCall => p.1) := Computable.fst
  have hq : Computable (fun p : PredicateCall => p.2 / 8) := (quotient_primitive 8).to_comp.comp Computable.snd
  have hl : Computable (fun p : PredicateCall => (p.2 / 8).unpair.1) := (left_primitive 8).to_comp.comp Computable.snd
  have hr : Computable (fun p : PredicateCall => (p.2 / 8).unpair.2) := (right_primitive 8).to_comp.comp Computable.snd
  have hn : Computable (fun p : PredicateCall => p.1 + ExpandedGraphCode.nodeCount (forest (p.2 / 8).unpair.1)) :=
    Primrec.nat_add.to_comp.comp hs
      (ExpandedGraphCodeProof.nodeCount_computable.comp (forest_computable.comp hl))
  exact ComputableMapAtomsProof.computable_ite
    (((tag_is 8 0).or ((tag_is 8 1).or ((tag_is 8 2).or ((tag_is 8 3).or (tag_is 8 4))))).comp Primrec.snd)
    (Computable.const [])
    (ComputableMapAtomsProof.computable_ite ((tag_is 8 5).comp Primrec.snd)
      (Primrec.list_cons.to_comp.comp (hs.pair hq) (Computable.const []))
      (Primrec.list_cons.to_comp.comp (hs.pair hl)
        (Primrec.list_cons.to_comp.comp (hn.pair hr) (Computable.const []))))

theorem predicateChildren_decreasing : ∀ (p child : PredicateCall),
    child ∈ predicateChildren p → child.2 < p.2 := by
  intro p child h
  by_cases hleaf : p.2 % 8 = 0 ∨ p.2 % 8 = 1 ∨ p.2 % 8 = 2 ∨ p.2 % 8 = 3 ∨ p.2 % 8 = 4
  · simp [predicateChildren, hleaf] at h
  have hp : 0 < p.2 := by omega
  have hd : p.2 / 8 < p.2 := Nat.div_lt_self hp (by decide)
  have hl := Nat.unpair_left_le (p.2 / 8)
  have hr := Nat.unpair_right_le (p.2 / 8)
  rcases child with ⟨nextStart, nextCode⟩
  unfold predicateChildren at h
  split_ifs at h <;> simp_all only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq]
  all_goals omega

theorem predicateAssemble_computable : Computable₂ predicateAssemble := by
  let A := PredicateCall × List Nat
  have hs : Computable (fun p : A => p.1.1) := Computable.fst.comp Computable.fst
  have hc : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hl : Primrec (fun p : A => (p.1.2 / 8).unpair.1) := (left_primitive 8).comp hc
  have hr : Primrec (fun p : A => (p.1.2 / 8).unpair.2) := (right_primitive 8).comp hc
  have h0 : Computable (fun p : A => p.2.getD 0 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd (Computable.const 0)
  have h1 : Computable (fun p : A => p.2.getD 1 0) :=
    (Primrec.list_getD (0 : Nat)).to_comp.comp Computable.snd (Computable.const 1)
  have hn : Computable (fun p : A => p.1.1 + ExpandedGraphCode.nodeCount (p.1.2 / 8).unpair.1) :=
    Primrec.nat_add.to_comp.comp hs (ExpandedGraphCodeProof.nodeCount_computable.comp hl.to_comp)
  have hx : Computable (fun p : A => ExpandedGraphCode.output p.1.1 (p.1.2 / 8).unpair.1) :=
    ExpandedGraphCodeProof.output_computable.comp hs hl.to_comp
  have hy : Computable (fun p : A => ExpandedGraphCode.output
      (p.1.1 + ExpandedGraphCode.nodeCount (p.1.2 / 8).unpair.1) (p.1.2 / 8).unpair.2) :=
    ExpandedGraphCodeProof.output_computable.comp hn hr.to_comp
  have hz : Computable (fun p : A => ExpandedGraphCode.output p.1.1 (p.1.2 / 8).unpair.2) :=
    ExpandedGraphCodeProof.output_computable.comp hs hr.to_comp
  have hstrict : Primrec (fun p : A => p.1.2 % 8 == 3) := by
    apply (((tag_is 8 3).comp hc).decide).of_eq
    intro p
    by_cases h : p.1.2 % 8 = 3 <;> simp [h]
  have hrel : Computable (fun p : A => SourceRows.Code.relation (p.1.2 % 8 == 3)
      (ExpandedGraphCode.output p.1.1 (p.1.2 / 8).unpair.1)
      (ExpandedGraphCode.output (p.1.1 + ExpandedGraphCode.nodeCount (p.1.2 / 8).unpair.1) (p.1.2 / 8).unpair.2)) :=
    SourceRowsCodeProof.relation_primitive.to_comp.comp (hstrict.to_comp.pair (hx.pair hy))
  have hrow : Computable (fun p : A => ((0 : Int), [(1 : Int,
      SourceTermGraph.Code.variableData (ExpandedGraphCode.output p.1.1 (p.1.2 / 8).unpair.2))])) :=
    (Computable.const (0 : Int)).pair
      (Primrec.list_cons.to_comp.comp
        ((Computable.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.to_comp.comp hz))
        (Computable.const []))
  have hzdiv := SourceTermGraphCodeProof.equation_primitive.to_comp.comp hrow
  have hndiv : Computable (fun p : A => 6 * Encodable.encode
      ((1, (p.1.2 / 8).unpair.1 - 1, (0 : Int), [(1 : Int,
        SourceTermGraph.Code.variableData (ExpandedGraphCode.output p.1.1 (p.1.2 / 8).unpair.2))]) : NormalForm.Code.AtomData) + 2) :=
    (unary_primitive 6 2).to_comp.comp
      (Primrec.encode.to_comp.comp ((Computable.const 1).pair
        ((Primrec.nat_sub.to_comp.comp hl.to_comp (Computable.const 1)).pair hrow)))
  have hdiv := ComputableMapAtomsProof.computable_ite
    (Primrec.eq.comp hl (Primrec.const 0)) hzdiv hndiv
  have hneg := (unary_primitive 6 3).to_comp.comp h0
  have hbin : Computable (fun p : A => 6 * Nat.pair (p.2.getD 0 0) (p.2.getD 1 0) + (p.1.2 % 8 - 2)) :=
    Primrec.nat_add.to_comp.comp
      (Primrec.nat_mul.to_comp.comp (Computable.const 6) (Primrec₂.natPair.to_comp.comp h0 h1))
      (Primrec.nat_sub.to_comp.comp
        (Primrec.nat_mod.to_comp.comp hc.to_comp (Computable.const 8)) (Computable.const 2))
  change Computable (fun p : A => predicateAssemble p.1 p.2)
  unfold predicateAssemble
  exact ComputableMapAtomsProof.computable_ite ((tag_is 8 0).comp hc) (Computable.const 0)
    (ComputableMapAtomsProof.computable_ite ((tag_is 8 1).comp hc) (Computable.const 1)
      (ComputableMapAtomsProof.computable_ite (((tag_is 8 2).or (tag_is 8 3)).comp hc) hrel
        (ComputableMapAtomsProof.computable_ite ((tag_is 8 4).comp hc) hdiv
          (ComputableMapAtomsProof.computable_ite ((tag_is 8 5).comp hc) hneg hbin))))

theorem predicate_equation (p : PredicateCall) : predicate p.1 p.2 =
    predicateAssemble p ((predicateChildren p).map (fun q => predicate q.1 q.2)) := by
  rw [predicate]
  split_ifs <;> simp_all [predicateChildren, predicateAssemble]

theorem predicate_computable : Computable₂ predicate := by
  classical
  exact (FiniteGraph.Proof.exactDecreasingGraph PredicateCall Nat predicateChildren predicateAssemble
    Prod.snd predicateChildren_computable predicateAssemble_computable Computable.snd
    (fun p => predicate p.1 p.2) predicateChildren_decreasing predicate_equation).2

theorem compile_computable : Computable₂ compile :=
  SourceTermGraphCodeProof.conjunction_primitive.to_comp.comp
    (ExpandedGraphCodeProof.graph_computable.comp startFor_computable
      (forest_computable.comp Computable.snd))
    (predicate_computable.comp startFor_computable Computable.snd)

theorem actualPrograms : BooleanGraphCodeTargets.ActualPrograms :=
  ⟨termVariables_computable, forest_computable, predicate_computable,
    startFor_computable, allocated_computable, compile_computable⟩

#print axioms predicateChildren_computable
#print axioms predicateChildren_decreasing
#print axioms predicateAssemble_computable
#print axioms predicate_equation
#print axioms predicate_computable
#print axioms compile_computable
#print axioms actualPrograms
end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SixSol20261112.BooleanGraphCodeProof
