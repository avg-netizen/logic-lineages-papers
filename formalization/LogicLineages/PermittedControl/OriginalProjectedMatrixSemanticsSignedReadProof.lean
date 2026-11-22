module
public import LogicLineages.PermittedControl.OriginalProjectedMatrixSemanticsTargets
import LogicLineages.PermittedControl.PreparedParameterActualProof

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalProjectedMatrixSemantics
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperand LowerOperandActual lowerOperandRead PreparedTableTied preparedTiedProjection)
open OriginalProjectedMatrixDecode (Summand LiteralTerm LiteralRow testOf)
open MixedSameRankResidue (WeightedOperand orderedReads actualSum)
open SignedRowSliceValue (valueAt)
open HeterogeneousSignedMatrixSlice (Row Snapshot actualRows)
open OriginalPlainTerminalMatrix (atomAnswer)
open SignedRowGuardedTest (Test)

private theorem checkedTerm (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat)
    (fit : PreparedTableTied f top ρ ops ν) (s : Summand) (t : WeightedOperand) (literal : LiteralTerm ops s t) :
    t.1 = s.1 ∧ LowerOperandActual f ρ t.2 (s.2.term.value ν) ∧
      lowerOperandRead f ρ t.2 = some (some (s.2.term.value ν)) := by
  obtain ⟨j,hj,shape,eq⟩ := literal
  have actual := (fit j hj).2
  change LowerOperandActual f ρ ops[j] (ν (j+1)) at actual
  rw [eq,shape]
  exact ⟨rfl,actual,(preparedTiedProjection.1 f ρ ops[j] _).mpr actual⟩

private theorem readValues (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat)
    (fit : PreparedTableTied f top ρ ops ν) {source : List Summand} {terms : List WeightedOperand}
    (literal : List.Forall₂ (LiteralTerm ops) source terms) (values : List Nat) :
    orderedReads f ρ terms values ↔ values = source.map (fun s => s.2.term.value ν) := by
  induction literal generalizing values with
  | nil => cases values <;> simp [orderedReads]
  | @cons s t ss ts head tail ih =>
      cases values with
      | nil => simp [orderedReads]
      | cons v rest =>
          obtain ⟨_,actual,hit⟩ := checkedTerm f ρ top ops ν fit s t head
          constructor
          · intro seen
            have exactHead : s.2.term.value ν = v := Option.some.inj (Option.some.inj (hit.symm.trans seen.2.1))
            exact congrArg₂ List.cons exactHead.symm ((ih rest).mp seen.2.2)
          · intro eq
            have parts := List.cons.inj eq
            rw [parts.1]
            exact ⟨actual,hit,(ih rest).mpr parts.2⟩

private theorem sums (ops : List LowerOperand) (ν : Nat → Nat) {source : List Summand}
    {terms : List WeightedOperand} (literal : List.Forall₂ (LiteralTerm ops) source terms) :
    actualSum terms (source.map (fun s => s.2.term.value ν)) =
      (source.map (fun s => s.1 * (s.2.term.value ν : Int))).sum := by
  induction literal with
  | nil => rfl
  | @cons s t ss ts head tail ih =>
      obtain ⟨j,hj,shape,eq⟩ := head
      change t.1 * (s.2.term.value ν : Int) + actualSum ts (ss.map (fun s => s.2.term.value ν)) =
        s.1 * (s.2.term.value ν : Int) + (ss.map (fun s => s.1 * (s.2.term.value ν : Int))).sum
      rw [eq,ih] <;> rfl

private theorem valueCorrect (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat)
    (fit : PreparedTableTied f top ρ ops ν) (a : NormalForm.Atom) (row : Row)
    (literal : LiteralRow ops a row) (v : Int) :
    valueAt f ρ row.2.1 row.2.2 v ↔ NormalForm.rowValue a.row ν = v := by
  have eq := sums ops ν literal.2.2
  constructor
  · rintro ⟨vs,seen,computed⟩
    rw [(readValues f ρ top ops ν fit literal.2.2 vs).mp seen,literal.2.1,eq] at computed
    exact computed
  · intro h
    refine ⟨_,(readValues f ρ top ops ν fit literal.2.2 _).mpr rfl,?_⟩
    rw [literal.2.1,eq]
    exact h

private theorem atomBit (ν : Nat → Nat) (a : NormalForm.Atom) (bit : Bool) :
    (testOf a).atPolarity bit (NormalForm.rowValue a.row ν) ↔ bit = atomAnswer ν a := by
  have calibrate (P : Prop) [Decidable P] :
      (if bit then P else ¬P) ↔ bit = decide P := by
    cases bit <;> by_cases h : P <;> simp [h]
  cases a with
  | nonnegative r => exact calibrate (0 ≤ NormalForm.rowValue r ν)
  | divisible m r =>
      change (if bit then ((m+1 : Nat) : Int) ∣ NormalForm.rowValue r ν
        else ¬ ((m+1 : Nat) : Int) ∣ NormalForm.rowValue r ν) ↔
          bit = decide (NormalForm.rowValue r ν % ((m+1 : Nat) : Int) = 0)
      rw [Int.dvd_iff_emod_eq_zero]
      exact calibrate _

theorem literalSnapshot (f ρ : Nat → Nat) (top : Nat) (ops : List LowerOperand) (ν : Nat → Nat)
    (fit : PreparedTableTied f top ρ ops ν) (a : NormalForm.Atom) (row : Row)
    (literal : LiteralRow ops a row) (v : Int) (b : Bool) :
    (row.1.Admitted ∧ valueAt f ρ row.2.1 row.2.2 v ∧ row.1.atPolarity b v) ↔
      (v,b) = (NormalForm.rowValue a.row ν,atomAnswer ν a) := by
  have read := valueCorrect f ρ top ops ν fit a row literal v
  have can : (testOf a).Admitted := by
    cases a with
    | nonnegative r => trivial
    | divisible m r => exact Nat.succ_pos m
  constructor
  · rintro ⟨_,actual,bit⟩
    have eq := read.mp actual
    rw [literal.1,← eq] at bit
    exact Prod.ext eq.symm ((atomBit ν a b).mp bit)
  · intro both
    have val : v = NormalForm.rowValue a.row ν := congrArg Prod.fst both
    have bit : b = atomAnswer ν a := congrArg Prod.snd both
    refine ⟨literal.1.symm ▸ can,read.mpr val.symm,?_⟩
    rw [literal.1,val]
    exact (atomBit ν a b).mpr bit

end LogicLineages.PermittedControl.OriginalProjectedMatrixSemantics
