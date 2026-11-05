module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsCompilerProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadGuardProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsProof
open NormalForm ShiftedInputGuards ShiftedInputPrograms

theorem occurrences_primitive : Primrec Code.occurrences := by
  let Item := Int × NormalForm.Code.ItemData
  have hp : PrimrecPred (fun a : Item => a.2.1 = 1) :=
    Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)
  have hf : Primrec (fun r : NormalForm.Code.RowData => r.2.filter (fun a => a.2.1 == 1)) := by
    apply ((Primrec.listFilter hp).comp Primrec.snd).of_eq
    intro r
    apply congrArg (fun f : Item → Bool => r.2.filter f)
    funext a
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq, beq_iff_eq]
  have he : Primrec (fun p : NormalForm.Code.RowData × Item =>
      (p.2.1, p.2.2.2.1, p.2.2.2.2.1)) :=
    (Primrec.fst.comp Primrec.snd).pair
      ((Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))).pair
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact Primrec.list_map hf he.to₂

theorem coefficients_primitive : Primrec Code.coefficients :=
  Primrec.list_map occurrences_primitive (Primrec.fst.comp Primrec.snd).to₂

theorem inputs_primitive : Primrec Code.inputs :=
  Primrec.list_map occurrences_primitive (Primrec.snd.comp Primrec.snd).to₂

theorem canceled_primitive : Primrec Code.canceled :=
  compile_primitive.comp inputs_primitive
    (CommonHeadCode.Program.canceled_primitive.comp coefficients_primitive)

theorem block_primitive :
    Primrec (fun p : NormalForm.Code.RowData × Nat × Int => Code.block p.1 p.2.1 p.2.2) :=
  compile_primitive.comp (inputs_primitive.comp Primrec.fst)
    (CommonHeadCode.Program.block_primitive.comp
      ((coefficients_primitive.comp Primrec.fst).pair
        ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))))

theorem activeSign_primitive : Primrec₂ Code.activeSign :=
  compile_primitive.comp (inputs_primitive.comp Primrec.fst)
    (CommonHeadCode.Program.sign_primitive_code.comp
      ((Primrec.const 0).pair ((coefficients_primitive.comp Primrec.fst).pair Primrec.snd)))

theorem actualSourceGuardPrograms : ShiftedInputProgramsTargets.ActualSourceGuardPrograms :=
  ⟨occurrences_primitive, coefficients_primitive, inputs_primitive,
    canceled_primitive, block_primitive, activeSign_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsProof
