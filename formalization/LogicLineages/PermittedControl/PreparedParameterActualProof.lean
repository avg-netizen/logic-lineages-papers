module
public import LogicLineages.PermittedControl.PreparedParameterProjectionTargets
import LogicLineages.PermittedControl.PreparedParameterOutputProof
import LogicLineages.PermittedControl.ClosedOrdinaryFieldActualProof
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsSemanticStatementChecks

@[expose] public section
namespace LogicLineages.PermittedControl.PreparedProjection
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open FieldComparison

theorem preparedProjectionActual : PreparedProjectionActual := by
  intro table p hp ν
  exact LinearRowsSemanticStatementChecks.actual_linear_elimination 0 p
    (preparedProjectionSyntax table p hp).1 ν

private theorem lower_read_hit (f : Nat → Nat) (ρ : Nat → Nat) (op : LowerOperand) (v : Nat) :
    lowerOperandRead f ρ op = some (some v) ↔ LowerOperandActual f ρ op v := by
  classical
  cases op with
  | coordinate rank => simp [lowerOperandRead,LowerOperandActual,eq_comm]
  | ordinary rank F =>
    simp only [lowerOperandRead,LowerOperandActual]
    have h := closedOrdinaryValueActual f F (ρ rank)
    constructor
    · intro hhit
      have hd : ClosedOrdinaryValueDomain F (ρ rank) := by
        by_contra hn
        have hnone := h.1.mpr hn
        rw [hhit] at hnone
        cases hnone
      exact ⟨hd,((h.2 hd).1 v).mp hhit⟩
    · rintro ⟨hd,hval⟩
      exact ((h.2 hd).1 v).mpr hval
  | count rank lam mu =>
    simp only [lowerOperandRead,LowerOperandActual]
    have h := closedOrdinaryCountActual f lam mu (ρ rank)
    constructor
    · intro hhit
      have hd : ClosedOrdinaryValueDomain (.entry 0 lam mu) (ρ rank) := by
        by_contra hn
        have hnone := h.1.mpr hn
        rw [hhit] at hnone
        cases hnone
      exact ⟨hd,((h.2 hd).1 v).mp hhit⟩
    · rintro ⟨hd,hval⟩
      exact ((h.2 hd).1 v).mpr hval

private theorem lower_actual_update (f : Nat → Nat) (ρ : Nat → Nat)
    (zRank z : Nat) (op : LowerOperand) (v : Nat) (hr : op.rank < zRank) :
    LowerOperandActual f (Function.update ρ zRank z) op v ↔ LowerOperandActual f ρ op v := by
  cases op with
  | coordinate rank =>
    have hne : rank ≠ zRank := ne_of_lt hr
    simp only [LowerOperandActual,Function.update_of_ne hne]
  | ordinary rank F =>
    have hne : rank ≠ zRank := ne_of_lt hr
    simp only [LowerOperandActual,Function.update_of_ne hne]
  | count rank lam mu =>
    have hne : rank ≠ zRank := ne_of_lt hr
    simp only [LowerOperandActual,Function.update_of_ne hne]

private theorem tied_update (f : Nat → Nat) (zRank : Nat) (ρ : Nat → Nat)
    (table : List LowerOperand) (ν : Nat → Nat)
    (ht : PreparedTableTied f zRank ρ table ν) (z : Nat) :
    PreparedTableTied f zRank (Function.update ρ zRank z) table (Function.update ν 0 z) := by
  intro j hj
  let op := table.get ⟨j,hj⟩
  have h := ht j hj
  refine ⟨h.1,?_⟩
  change LowerOperandActual f (Function.update ρ zRank z) op (Function.update ν 0 z (j+1))
  rw [Function.update_of_ne (Nat.succ_ne_zero j)]
  exact (lower_actual_update f ρ zRank z op _ h.1).mpr h.2

theorem preparedTiedProjection : PreparedTiedProjection := by
  refine ⟨lower_read_hit,?_⟩
  intro f zRank ρ table p ν hp ht
  have hupdate := tied_update f zRank ρ table ν ht
  refine ⟨hupdate,?_⟩
  constructor
  · intro h
    obtain ⟨z,hz⟩ := (preparedProjectionActual table p hp ν).mp h
    exact ⟨z,hupdate z,hz⟩
  · rintro ⟨z,_,hz⟩
    exact (preparedProjectionActual table p hp ν).mpr ⟨z,hz⟩

end LogicLineages.PermittedControl.PreparedProjection
