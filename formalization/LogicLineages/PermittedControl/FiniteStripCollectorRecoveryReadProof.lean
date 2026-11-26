module
public import LogicLineages.PermittedControl.FiniteStripCollectorRecoveryTargets

@[expose] public section
namespace LogicLineages.PermittedControl.FiniteStripCollectorRecovery
open OrdinalComparison PreparedProjection FieldComparison

theorem shape_code (op : LowerOperand) : operandShape op.code = true := by
  cases op with
  | coordinate rank => simp [LowerOperand.code,operandShape]
  | ordinary rank F => cases F <;> simp [LowerOperand.code,longFieldCode,operandShape]
  | count rank lam mu => simp [LowerOperand.code,longFieldCode,operandShape]

private theorem code_rank (op : LowerOperand) : op.code.2.1 = op.rank := by
  cases op <;> rfl

private theorem field_code (f : Nat → Nat) (a : Nat) (op : LowerOperand) :
    fieldRead f a op.code = lowerOperandRead f (fun _ => a) op := by
  cases op <;> simp [fieldRead,LowerOperand.code,lowerOperandRead,longFieldCode]

theorem read_code (f : Nat → Nat) (x a : Nat) (r : NamedOperand) :
    readCode f x a (encodeRequest r) = expectedRead f x a r := by
  rcases r with ⟨name,op⟩
  simp only [readCode,encodeRequest,shape_code,Bool.true_eq_false,or_false,
    expectedRead,code_rank,field_code]

theorem collect_code (f : Nat → Nat) (x a : Nat) (rs : List NamedOperand) :
    collectCode f x a (rs.map encodeRequest) = expectedCollect f x a rs := by
  induction rs with
  | nil => rfl
  | cons r rs ih =>
    change appendResult (readCode f x a (encodeRequest r))
      (collectCode f x a (rs.map encodeRequest)) =
      appendResult (expectedRead f x a r) (expectedCollect f x a rs)
    rw [read_code,ih]

theorem collectorReadExact : CollectorReadExact := ⟨shape_code,read_code,collect_code⟩
end LogicLineages.PermittedControl.FiniteStripCollectorRecovery
