module
public import LogicLineages.PermittedControl.InverseComparisonPreparedRowsTargets

@[expose] public section
namespace LogicLineages.PermittedControl.InverseComparisonPreparedRows
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection

private theorem preparedAtom (operand : LowerOperand) (c : Int) (first second : Nat)
    (firstBound : first ≤ 1) (secondBound : second ≤ 1) :
    PreparedInput [operand] (.atom (.nonnegative (c,[(1,.variable first),(-1,.variable second)]))) := by
  constructor
  · intro a member s used
    have onlyAtom : a = .nonnegative (c,[(1,.variable first),(-1,.variable second)]) := by
      simpa only [LinearRows.atoms,List.mem_singleton] using member
    subst a
    change s ∈ [(1,.variable first),(-1,.variable second)] at used
    rcases List.mem_cons.mp used with head | tail
    · subst s
      exact ⟨first,rfl⟩
    · have last := List.mem_singleton.mp tail
      subst s
      exact ⟨second,rfl⟩
  · intro i used
    change i ∈ [first,second] at used
    change i ≤ 1
    rcases List.mem_cons.mp used with head | tail
    · simpa only [head] using firstBound
    · simpa only [List.mem_singleton.mp tail] using secondBound

private theorem preparedPair (operand : LowerOperand) (p q : NormalForm.Formula)
    (hp : PreparedInput [operand] p) (hq : PreparedInput [operand] q) :
    PreparedInput [operand] (.conjunction p q) := by
  constructor
  · intro a member s used
    rcases List.mem_append.mp member with left | right
    · exact hp.1 a left s used
    · exact hq.1 a right s used
  · intro i used
    rcases List.mem_append.mp used with left | right
    · exact hp.2 i left
    · exact hq.2 i right

theorem preparedShape : PreparedShape := by
  intro sign wanted operand
  have positive (c : Int) : PreparedInput [operand] (greaterMinusParameter c) :=
    preparedAtom operand c 0 1 (by decide) le_rfl
  have negative (c : Int) : PreparedInput [operand] (parameterMinusGreater c) :=
    preparedAtom operand c 1 0 le_rfl (by decide)
  have equal : PreparedInput [operand] equalRows :=
    preparedPair operand _ _ (positive 0) (negative 0)
  have impossible : PreparedInput [operand] .falsity := by
    constructor
    · intro a member
      exact (List.not_mem_nil member).elim
    · intro i used
      exact (List.not_mem_nil used).elim
  unfold emitFormula
  split_ifs <;> (first | exact positive _ | exact negative _ | exact equal | exact impossible)

end LogicLineages.PermittedControl.InverseComparisonPreparedRows
