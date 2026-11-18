module
public import LogicLineages.ControlSensitivityCurrent.RawCheckedRenamingTargets
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorPrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGRawValidatorEquivalenceProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsPrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedRenaming

theorem scan_entry_primitive :
    Primrec (fun p : List Nat × Option (List Nat) × Nat => scanEntry p.1 p.2.1 p.2.2) := by
  let A := List Nat × Option (List Nat) × Nat
  let B := A × List Nat
  let C := B × (Nat × List Nat)
  have htarget : Primrec (fun p : C => p.1.1.1) :=
    Primrec.fst.comp (Primrec.fst.comp Primrec.fst)
  have htype : Primrec (fun p : C => p.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have hindex : Primrec (fun p : C => p.2.1) := Primrec.fst.comp Primrec.snd
  have htail : Primrec (fun p : C => p.2.2) := Primrec.snd.comp Primrec.snd
  have hcons := Primrec.cond (RawValidator.variable_primitive.comp (htarget.pair (htype.pair hindex)))
    (Primrec.option_some.comp htail) (Primrec.const none)
  have hread : Primrec₂ (fun (p : A) (xs : List Nat) =>
      match xs with
      | [] => none
      | i :: rest => if RawValidator.«variable» p.1 p.2.2 i then some rest else none) := by
    apply Primrec.to₂
    apply (Primrec.list_casesOn (α := B) Primrec.snd (Primrec.const none) hcons.to₂).of_eq
    intro p
    cases p.2 <;> rfl
  apply (Primrec.option_bind (Primrec.fst.comp (Primrec.snd : Primrec (fun p : A => p.2))) hread).of_eq
  intro p
  rcases p with ⟨target, remaining, sourceType⟩
  rcases remaining with _ | (_ | ⟨i, rest⟩) <;> rfl

theorem table_guard_primitive :
    Primrec (fun p : List Nat × List Nat × List Nat => tableGuard p.1 p.2.1 p.2.2) := by
  let A := List Nat × List Nat × List Nat
  let B := A × (Option (List Nat) × Nat)
  have htarget : Primrec (fun p : B => p.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hrest : Primrec (fun p : B => p.2) := Primrec.snd
  have hfold := Primrec.list_foldl (Primrec.fst : Primrec (fun p : A => p.1))
    (Primrec.option_some.comp (Primrec.snd.comp Primrec.snd))
    (scan_entry_primitive.comp (htarget.pair hrest)).to₂
  exact (Primrec.eq.comp hfold (Primrec.const (some ([] : List Nat)))).decide

theorem effective : RawCheckedRenamingTargets.Effective := by
  let A := List Nat × List Nat × Code
  have htarget : Primrec (fun p : A => p.1) := Primrec.fst
  have htable : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hcode : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hvalid := RawValidator.check_primitive.of_eq RawValidator.check_eq_valid
  have hg : Primrec (fun p : A => guard p.1 p.2.1 p.2.2) :=
    Primrec.and.comp (hvalid.comp hcode)
      (table_guard_primitive.comp ((Primrec.fst.comp hcode).pair (htarget.pair htable)))
  apply (Computable.cond hg.to_comp
    (Computable.option_some.comp Operations.rename_code_primitive.to_comp)
    (Computable.const none)).of_eq
  intro p
  cases h : guard p.1 p.2.1 p.2.2 <;> simp [rename, h]

end LogicLineages.ControlSensitivityCurrent.RawSourceDAG.CheckedRenaming
