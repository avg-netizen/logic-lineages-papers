module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
open ExpandedGraphCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem disjunction_primitive : Primrec₂ disjunction :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 5)
#print axioms disjunction_primitive

theorem multiplyRow_primitive : Primrec (fun p : Nat × Nat × Nat => multiplyRow p.1 p.2.1 p.2.2) := by
  let C := Nat × Nat × Nat
  have hz : Primrec (fun p : C => p.1) := Primrec.fst
  have hx : Primrec (fun p : C => p.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun p : C => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p : C => (p.2.2 : Int)) := IntegerAlgorithms.Proof.ofNat_primitive.comp hy
  have hnc : Primrec (fun p : C => -(p.2.2 : Int)) := IntegerAlgorithms.Proof.negate_primitive.comp hc
  exact (Primrec.const (0 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hz)) (Primrec.list_cons.comp (hnc.pair (SourceTermGraphCodeProof.variableData_primitive.comp hx)) (Primrec.const [])))
#print axioms multiplyRow_primitive

theorem subtraction_primitive : Primrec (fun p : Nat × Nat × Nat => subtraction p.1 p.2.1 p.2.2) := by
  let C := Nat × Nat × Nat
  have hz : Primrec (fun p : C => p.1) := Primrec.fst
  have hx : Primrec (fun p : C => p.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun p : C => p.2.2) := Primrec.snd.comp Primrec.snd
  have ha : Primrec (fun p : C => ((0, [(1, SourceTermGraph.Code.variableData p.2.2), (-1, SourceTermGraph.Code.variableData p.2.1)]) : RowData)) :=
    (Primrec.const (0 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hy)) (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hx)) (Primrec.const [])))
  have hb : Primrec (fun p : C => ((0, [(1, SourceTermGraph.Code.variableData p.1)]) : RowData)) :=
    (Primrec.const (0 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hz)) (Primrec.const []))
  have hc : Primrec (fun p : C => ((-1, [(1, SourceTermGraph.Code.variableData p.2.1), (-1, SourceTermGraph.Code.variableData p.2.2)]) : RowData)) :=
    (Primrec.const (-1 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hx)) (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hy)) (Primrec.const [])))
  have hd : Primrec (fun p : C => ((0, [(1, SourceTermGraph.Code.variableData p.2.1), (-1, SourceTermGraph.Code.variableData p.2.2), (-1, SourceTermGraph.Code.variableData p.1)]) : RowData)) :=
    (Primrec.const (0 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hx)) (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hy)) (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hz)) (Primrec.const []))))
  exact disjunction_primitive.comp
    (SourceTermGraphCodeProof.conjunction_primitive.comp
      (SourceTermGraphCodeProof.atom_primitive.comp ha) (SourceTermGraphCodeProof.equation_primitive.comp hb))
    (SourceTermGraphCodeProof.conjunction_primitive.comp
      (SourceTermGraphCodeProof.atom_primitive.comp hc) (SourceTermGraphCodeProof.equation_primitive.comp hd))
#print axioms subtraction_primitive

theorem division_primitive : Primrec (fun p : Nat × Nat × Nat => division p.1 p.2.1 p.2.2) := by
  let C := Nat × Nat × Nat
  have hz : Primrec (fun p : C => p.1) := Primrec.fst
  have hx : Primrec (fun p : C => p.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun p : C => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p : C => (p.2.2 : Int)) := IntegerAlgorithms.Proof.ofNat_primitive.comp hy
  have hnc : Primrec (fun p : C => -(p.2.2 : Int)) := IntegerAlgorithms.Proof.negate_primitive.comp hc
  have hcm : Primrec (fun p : C => (p.2.2 : Int) - 1) := by
    simpa only [sub_eq_add_neg] using IntegerAlgorithms.Proof.add_primitive.comp hc (Primrec.const (-1 : Int))
  have ha : Primrec (fun p : C => ((0, [(1, SourceTermGraph.Code.variableData p.1)]) : RowData)) :=
    (Primrec.const (0 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hz)) (Primrec.const []))
  have hb : Primrec (fun p : C => ((0, [(1, SourceTermGraph.Code.variableData p.2.1), (-(p.2.2 : Int), SourceTermGraph.Code.variableData p.1)]) : RowData)) :=
    (Primrec.const (0 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hx)) (Primrec.list_cons.comp (hnc.pair (SourceTermGraphCodeProof.variableData_primitive.comp hz)) (Primrec.const [])))
  have hd : Primrec (fun p : C => (((p.2.2 : Int) - 1, [((p.2.2 : Int), SourceTermGraph.Code.variableData p.1), (-1, SourceTermGraph.Code.variableData p.2.1)]) : RowData)) :=
    hcm.pair (Primrec.list_cons.comp (hc.pair (SourceTermGraphCodeProof.variableData_primitive.comp hz)) (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hx)) (Primrec.const [])))
  exact Primrec.ite (Primrec.eq.comp hy (Primrec.const 0))
    (SourceTermGraphCodeProof.equation_primitive.comp ha)
    (SourceTermGraphCodeProof.conjunction_primitive.comp
      (SourceTermGraphCodeProof.atom_primitive.comp hb) (SourceTermGraphCodeProof.atom_primitive.comp hd))
#print axioms division_primitive

theorem inverse_primitive : Primrec (fun p : Nat × Nat × Nat => inverse p.1 p.2.1 p.2.2) := by
  let C := Nat × Nat × Nat
  have hz : Primrec (fun p : C => p.1) := Primrec.fst
  have hx : Primrec (fun p : C => p.2.1) := Primrec.fst.comp Primrec.snd
  have hy : Primrec (fun p : C => p.2.2) := Primrec.snd.comp Primrec.snd
  have ha : Primrec (fun p : C => ((-1, [(1, SourceTermGraph.Code.variableData p.1), (-1, SourceTermGraph.Code.variableData p.2.1)]) : RowData)) :=
    (Primrec.const (-1 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hz)) (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hx)) (Primrec.const [])))
  have hb : Primrec (fun p : C => ((0, [(1, SourceTermGraph.Code.variableData p.2.1)]) : RowData)) :=
    (Primrec.const (0 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hx)) (Primrec.const []))
  have hc : Primrec (fun p : C => ((0, [(1, SourceTermGraph.Code.variableData p.2.2), (-1, SourceTermGraph.Code.phiData p.2.1)]) : RowData)) :=
    (Primrec.const (0 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hy)) (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair (SourceTermGraphCodeProof.phiData_primitive.comp hx)) (Primrec.const [])))
  have hd : Primrec (fun p : C => ((-1, [(1, SourceTermGraph.Code.phiData p.1), (-1, SourceTermGraph.Code.variableData p.2.2)]) : RowData)) :=
    (Primrec.const (-1 : Int)).pair (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair (SourceTermGraphCodeProof.phiData_primitive.comp hz)) (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair (SourceTermGraphCodeProof.variableData_primitive.comp hy)) (Primrec.const [])))
  exact SourceTermGraphCodeProof.conjunction_primitive.comp
    (SourceTermGraphCodeProof.equation_primitive.comp ha)
    (SourceTermGraphCodeProof.conjunction_primitive.comp
      (disjunction_primitive.comp (SourceTermGraphCodeProof.equation_primitive.comp hb)
        (SourceTermGraphCodeProof.atom_primitive.comp hc))
      (SourceTermGraphCodeProof.atom_primitive.comp hd))
#print axioms inverse_primitive


-- Explicit audits of the unchanged freshly compiled public supplier declarations.
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.variableData_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.phiData_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.numeralRow_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.variableRow_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.additionRow_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.phiRow_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.negateRow_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.atom_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.conjunction_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.equation_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.equations_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.emit_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.step_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.run_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.instructions_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.package_primitive
#print axioms LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeProof.actualNumericProgram

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.ExpandedGraphCodeProof
