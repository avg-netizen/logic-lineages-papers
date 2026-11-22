module
public import LogicLineages.PermittedControl.InverseComparisonPreparedRowsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.InverseComparisonPreparedRows
open OrdinalComparison.LayeredComparison.SnyatkovCompletion

private theorem codePrimitive : Primrec₂ emitCode := by
  let Input := Nat × Nat
  have sign (n : Nat) : PrimrecPred (fun p : Input => p.1 = n) :=
    Primrec.eq.comp Primrec.fst (Primrec.const n)
  have wanted (n : Nat) : PrimrecPred (fun p : Input => p.2 = n) :=
    Primrec.eq.comp Primrec.snd (Primrec.const n)
  have constant (p : NormalForm.Formula) : Primrec (fun _ : Input => p.encode) :=
    Primrec.const p.encode
  have no := constant .falsity
  have signZero := Primrec.ite (wanted 0) (constant (greaterMinusParameter 0))
    (Primrec.ite (wanted 2) (constant (parameterMinusGreater (-1))) no)
  have signOne := Primrec.ite (wanted 0) (constant (greaterMinusParameter (-1)))
    (Primrec.ite (wanted 1) (constant equalRows)
      (Primrec.ite (wanted 2) (constant (parameterMinusGreater (-1))) no))
  have signTwo := Primrec.ite (wanted 0) (constant (greaterMinusParameter (-1)))
    (Primrec.ite (wanted 2) (constant (parameterMinusGreater 0)) no)
  have compiled := Primrec.ite (sign 0) signZero
    (Primrec.ite (sign 1) signOne (Primrec.ite (sign 2) signTwo no))
  exact (compiled.of_eq (fun p : Input => show _ = emitCode p.1 p.2 from by
    unfold emitCode emitFormula
    split_ifs <;> rfl)).to₂

theorem formulaInvalid (sign wanted : Nat) (invalid : 2 < sign ∨ 2 < wanted) :
    emitFormula sign wanted = .falsity := by
  unfold emitFormula
  split_ifs <;> (first | rfl | omega)

theorem codeExact : CodeExact :=
  ⟨codePrimitive,fun sign wanted invalid => congrArg NormalForm.Formula.encode
    (formulaInvalid sign wanted invalid)⟩

end LogicLineages.PermittedControl.InverseComparisonPreparedRows
