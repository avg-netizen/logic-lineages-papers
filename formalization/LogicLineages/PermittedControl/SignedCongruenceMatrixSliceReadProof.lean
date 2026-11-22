module
public import LogicLineages.PermittedControl.SignedCongruenceMatrixSliceTargets
import LogicLineages.PermittedControl.SignedRowCoordinateSliceStatementChecks
import LogicLineages.PermittedControl.SignedRowCoordinateSliceReadProof

@[expose] public section
namespace LogicLineages.PermittedControl.SignedCongruenceMatrixSlice
open PreparedProjection SignedRowCoordinateSlice
open MixedSameRankResidue (WeightedOperand orderedReads)
open StatementChecks (fixed_signedRowCoordinateSliceFailureExact)

private theorem readMember (f ρ : Nat → Nat) (terms : List WeightedOperand) (values : List Nat)
    (reads : orderedReads f ρ terms values) (t : WeightedOperand) (mem : t ∈ terms) :
    ∃ v, lowerOperandRead f ρ t.2 = some (some v) := by
  induction terms generalizing values with
  | nil => simp at mem
  | cons h ts ih =>
    cases values with
    | nil => exact False.elim reads
    | cons v vs =>
      obtain ⟨_,read,more⟩ := reads
      rcases List.mem_cons.mp mem with first | later
      · subst t
        exact ⟨v,read⟩
      · exact ih vs more later

private theorem actualDomain (f : Nat → Nat) (a v : Nat) (op : LowerOperand)
    (value : LowerOperandActual f (fun _ => a) op v) : sourceDomain a op := by
  cases op with
  | coordinate _ => exact True.intro
  | ordinary _ _ => exact value.1
  | count _ _ _ => exact value.1

private theorem noFirstFailure (f ρ : Nat → Nat) (rank a : Nat) (terms : List WeightedOperand)
    (values : List Nat) (reads : orderedReads f ρ terms values) (agree : ρ rank = a)
    (kind : Failure) : ¬ firstFailure f rank a terms kind := by
  rintro ⟨earlier,t,later,whole,atRank,_,failed⟩
  have member : t ∈ terms := by simp [whole]
  obtain ⟨v,read⟩ := readMember f ρ terms values reads t member
  have constantRead := (sameCoordinateRead f ρ rank a t.2 atRank agree).symm.trans read
  have value := (hitRead f (fun _ => a) t.2 v).mp constantRead
  cases kind with
  | invalid => exact failed (actualDomain f a v t.2 value)
  | genuineMiss => exact failed.2 v value

theorem sliceExists (f ρ : Nat → Nat) (rank a : Nat) (c : Int)
    (terms : List WeightedOperand) (values : List Nat) (reads : orderedReads f ρ terms values)
    (agree : ρ rank = a) :
    ∃ (b : Int) (rest : List WeightedOperand), slice f rank a c terms = some (some (b,rest)) := by
  have statuses := fixed_signedRowCoordinateSliceFailureExact f rank a c terms
  cases result : slice f rank a c terms with
  | none => exact (noFirstFailure f ρ rank a terms values reads agree _ (statuses.1.mp result)).elim
  | some status =>
    cases status with
    | none => exact (noFirstFailure f ρ rank a terms values reads agree _ (statuses.2.mp result)).elim
    | some residual => exact ⟨residual.1,residual.2,by cases residual <;> rfl⟩

end LogicLineages.PermittedControl.SignedCongruenceMatrixSlice
