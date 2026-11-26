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
  have zero := Primrec.ite (wanted 0) (constant (greaterMinusParameter 0))
    (Primrec.ite (wanted 2) (constant (parameterMinusGreater (-1))) no)
  have one := Primrec.ite (wanted 0) (constant (greaterMinusParameter (-1)))
    (Primrec.ite (wanted 1) (constant equalRows)
      (Primrec.ite (wanted 2) (constant (parameterMinusGreater (-1))) no))
  have two := Primrec.ite (wanted 0) (constant (greaterMinusParameter (-1)))
    (Primrec.ite (wanted 2) (constant (parameterMinusGreater 0)) no)
  have compiled := Primrec.ite (sign 0) zero
    (Primrec.ite (sign 1) one (Primrec.ite (sign 2) two no))
  exact (compiled.of_eq (fun p : Input => by
    unfold emitCode emitFormula
    split_ifs <;> rfl)).to₂

theorem codeExact : CodeExact := by
  refine ⟨codePrimitive,?_⟩
  intro sign wanted invalid
  unfold emitCode emitFormula
  split_ifs <;> (first | rfl | omega)

end LogicLineages.PermittedControl.InverseComparisonPreparedRows
