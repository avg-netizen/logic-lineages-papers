module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceTermGraphCodeCalibrationProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeProof
open CommonLayerSyntax SourceRows

theorem bindAll_calibration (xs : List Nat) (p : QFormula) :
    Code.bindAll xs p.encode = (bindAll xs p).encode := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
      change 4 * Nat.pair i (Code.bindAll xs p.encode) + 3 =
        4 * Nat.pair i (bindAll xs p).encode + 3
      rw [ih]

theorem strictRow_data (x y : Nat) :
    NormalForm.rowData (strictRow x y) = Code.strictRow x y := rfl

theorem relation_calibration (strict : Bool) (x y : Nat) :
    Code.relation strict x y = (relation strict x y).encode := by
  cases strict with
  | false =>
      exact SourceTermGraphCodeProof.equation_calibration (SourceTermGraph.variableRow x y)
  | true => rfl

/-- The numeric atom uses exactly the typed postorder graph, both child
outputs, and the complete locally allocated list of witness binders. -/
theorem atom_calibration (strict : Bool) (a b : BaseTerm) :
    Code.atom strict a.encode b.encode = (localAtom strict a b).encode := by
  have hj : SourceTermGraph.Code.instructions (4 * Nat.pair a.encode b.encode + 2) =
      SourceTermGraph.instructions (.add a b) :=
    SourceTermGraphCodeProof.instructions_calibration (.add a b)
  have hr := SourceTermGraphCodeProof.rowMachineCalibration
    (.add a b) (localStart a b) [] []
  simp only [localStart] at hr
  simp only [Code.atom, SourceTermGraphCodeProof.instructions_calibration a,
    SourceTermGraphCodeProof.instructions_calibration b, hj]
  rw [hr]
  simp only [SourceTermGraphCodeProof.instructions_length, List.nil_append,
    SourceTermGraphCodeProof.equations_calibration, relation_calibration]
  change Code.bindAll (SourceTermGraph.allocated (localStart a b) (.add a b))
    (QFormula.matrix (atomBody strict a b)).encode = (localAtom strict a b).encode
  exact bindAll_calibration _ _

private theorem translate_step (n tag : Nat) (ht : tag < 5) :
    Code.translate (5 * n + tag) =
      if tag = 0 then Code.atom false n.unpair.1 n.unpair.2
      else if tag = 1 then Code.atom true n.unpair.1 n.unpair.2
      else if tag = 2 then 4 * Code.translate n + 1
      else if tag = 3 then
        4 * Nat.pair (Code.translate n.unpair.1) (Code.translate n.unpair.2) + 2
      else 4 * Nat.pair n.unpair.1 (Code.translate n.unpair.2) + 3 := by
  have hm : (5 * n + tag) % 5 = tag := by omega
  have hd : (5 * n + tag) / 5 = n := by omega
  rw [Code.translate, hm, hd]

theorem translate_calibration (p : SourceFormula) :
    Code.translate p.encode = (translate p).encode := by
  induction p with
  | equal a b =>
      simpa [SourceFormula.encode, translate, Nat.unpair_pair, atom_calibration] using
        translate_step (Nat.pair a.encode b.encode) 0 (by decide)
  | less a b =>
      simpa [SourceFormula.encode, translate, Nat.unpair_pair, atom_calibration] using
        translate_step (Nat.pair a.encode b.encode) 1 (by decide)
  | negative p hp =>
      simpa [SourceFormula.encode, translate, QFormula.encode, hp] using
        translate_step p.encode 2 (by decide)
  | conjunction p q hp hq =>
      simpa [SourceFormula.encode, translate, QFormula.encode, Nat.unpair_pair, hp, hq] using
        translate_step (Nat.pair p.encode q.encode) 3 (by decide)
  | existsNat i p hp =>
      simpa [SourceFormula.encode, translate, QFormula.encode, Nat.unpair_pair, hp] using
        translate_step (Nat.pair i p.encode) 4 (by decide)

theorem literalSourceCompilerCalibration : SourceRowsTargets.LiteralSourceCompilerCalibration :=
  translate_calibration

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeProof
