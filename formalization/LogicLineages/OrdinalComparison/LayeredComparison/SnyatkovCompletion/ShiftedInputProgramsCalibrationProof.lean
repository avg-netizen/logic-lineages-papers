module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsGuardEncodingProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsProof
open NormalForm ShiftedInputGuards ShiftedInputPrograms

theorem less_calibration (a b : Input) : Code.less a b = (ShiftedInputGuards.less a b).encode := rfl

theorem equal_calibration (a b : Input) : Code.equal a b = (ShiftedInputGuards.equal a b).encode := rfl

theorem bound_calibration (c : Nat) (a : Input) :
    Code.bound c a = (ShiftedInputGuards.bound c a).encode := by
  by_cases hc : c = 0 <;> simp [Code.bound, ShiftedInputGuards.bound, hc,
    Formula.encode, Atom.data, rowData, Summand.data, ShiftedInputPrograms.Code.atom, Code.varData]

theorem literalAtomicCodes : ShiftedInputProgramsTargets.LiteralAtomicCodes :=
  ⟨less_calibration, equal_calibration, bound_calibration⟩

private theorem run_append (xs : List Input) (p q : CommonHeadCode.Code) (stack : List Nat) :
    Code.run xs (p ++ q) stack = Code.run xs q (Code.run xs p stack) := List.foldl_append

private theorem run_encode (xs : List Input) (p : CommonHeadLargeGuards.Formula) (stack : List Nat) :
    Code.run xs (CommonHeadCompiler.encode p) stack =
      (ShiftedInputGuards.compile xs p).encode :: stack := by
  induction p generalizing stack with
  | truth => rfl
  | falsity => rfl
  | eq i j =>
      simp only [CommonHeadCompiler.encode, Code.run, List.foldl_cons, List.foldl_nil,
        Code.step, ShiftedInputGuards.compile, equal_calibration]
      rfl
  | lt i j =>
      simp only [CommonHeadCompiler.encode, Code.run, List.foldl_cons, List.foldl_nil,
        Code.step, ShiftedInputGuards.compile, less_calibration]
      rfl
  | bound c i =>
      simp only [CommonHeadCompiler.encode, Code.run, List.foldl_cons, List.foldl_nil,
        Code.step, ShiftedInputGuards.compile, bound_calibration]
      rfl
  | neg p ih =>
      simp only [CommonHeadCompiler.encode, run_append, ih]
      simp [Code.run, Code.step, Code.negative, ShiftedInputGuards.compile, Formula.encode]
  | conj p q ihp ihq =>
      simp only [CommonHeadCompiler.encode, run_append, ihp, ihq]
      simp [Code.run, Code.step, Code.conjunction, ShiftedInputGuards.compile, Formula.encode]
  | disj p q ihp ihq =>
      simp only [CommonHeadCompiler.encode, run_append, ihp, ihq]
      simp [Code.run, Code.step, Code.disjunction, ShiftedInputGuards.compile, Formula.encode]

theorem literalPostfixCompiler : ShiftedInputProgramsTargets.LiteralPostfixCompiler := by
  intro xs p
  unfold Code.compile
  rw [run_encode]
  rfl

theorem occurrences_calibration (r : Row) :
    Code.occurrences (rowData r) = ShiftedInputGuards.occurrences r := by
  rcases r with ⟨z, xs⟩
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      rcases a with ⟨w, s⟩
      cases s <;> simp [Code.occurrences, rowData, ShiftedInputGuards.occurrences,
        Summand.data] at ih ⊢ <;> exact ih

theorem coefficients_calibration (r : Row) :
    Code.coefficients (rowData r) = ShiftedInputGuards.coefficients r := by
  unfold Code.coefficients ShiftedInputGuards.coefficients
  rw [occurrences_calibration]

theorem inputs_calibration (r : Row) :
    Code.inputs (rowData r) = ShiftedInputGuards.inputs r := by
  unfold Code.inputs ShiftedInputGuards.inputs
  rw [occurrences_calibration]

theorem literalOriginalData : ShiftedInputProgramsTargets.LiteralOriginalData :=
  fun r => ⟨occurrences_calibration r, coefficients_calibration r, inputs_calibration r⟩

theorem literalGuardPrograms : ShiftedInputProgramsTargets.LiteralGuardPrograms := by
  refine ⟨?_, ?_, ?_⟩
  · intro r
    unfold Code.canceled ShiftedInputGuards.canceled
    rw [inputs_calibration, coefficients_calibration, GuardEncoding.canceled_code,
      literalPostfixCompiler]
  · intro r k desired
    unfold Code.block ShiftedInputGuards.block
    rw [inputs_calibration, coefficients_calibration, GuardEncoding.block_code,
      literalPostfixCompiler]
  · intro r desired
    unfold Code.activeSign ShiftedInputGuards.activeSign
    rw [inputs_calibration, coefficients_calibration, GuardEncoding.sign_code,
      literalPostfixCompiler]

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ShiftedInputProgramsProof
