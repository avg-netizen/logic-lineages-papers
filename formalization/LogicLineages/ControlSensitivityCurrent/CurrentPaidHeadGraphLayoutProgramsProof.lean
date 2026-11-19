module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphCompilerDefinitions
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphMatrixRenameProgramsProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open MatrixCode (atomProgram varProgram litProgram addProgram unaryProgram singleProgram pairListProgram)

theorem eqProgram : Primrec₂ MatrixCode.eq := atomProgram.comp ((Primrec.const 2).pair Primrec.id)
theorem leProgram : Primrec₂ MatrixCode.le := atomProgram.comp ((Primrec.const 3).pair Primrec.id)
theorem andProgram : Primrec₂ MatrixCode.both := atomProgram.comp ((Primrec.const 6).pair Primrec.id)
theorem orProgram : Primrec₂ MatrixCode.either := atomProgram.comp ((Primrec.const 7).pair Primrec.id)

theorem widthProgram : Primrec₂ directWidth := by
  let P := Nat×Nat
  have w : Primrec (fun q : P => q.1) := Primrec.fst
  have d : Primrec (fun q : P => q.2) := Primrec.snd
  exact Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp w (Primrec.const 3))
    (Primrec.succ.comp d)) d

theorem uProgram : Primrec₂ uSlot :=
  Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 3)) Primrec.snd

theorem argProgram : Primrec (fun q : Nat×Nat×Nat => argSlot q.1 q.2.1 q.2.2) :=
  Primrec.nat_add.comp (Primrec.nat_add.comp (Primrec.nat_add.comp Primrec.fst (Primrec.const 3))
    (Primrec.succ.comp (Primrec.fst.comp Primrec.snd))) (Primrec.snd.comp Primrec.snd)

private abbrev G := List Nat×Nat×Nat×Nat
private theorem gateCell : Primrec₂ (fun (q : G) (j : Nat) => MatrixCode.both
    (MatrixCode.eq (MatrixCode.var q.2.1) (MatrixCode.lit j))
    (MatrixCode.eq (MatrixCode.var q.2.2.1) (MatrixCode.lit (q.1.getD j 0)))) := by
  let P := G×Nat
  have u : Primrec (fun q : P => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have v : Primrec (fun q : P => q.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have y := (Primrec.list_getD 0).comp (Primrec.fst.comp Primrec.fst) Primrec.snd
  exact andProgram.comp (eqProgram.comp (varProgram.comp u) (litProgram.comp Primrec.snd))
    (eqProgram.comp (varProgram.comp v) (litProgram.comp y))

private theorem gateHigh : Primrec (fun (q : G) => MatrixCode.both
    (MatrixCode.eq (MatrixCode.var q.2.1) (MatrixCode.add (MatrixCode.var q.2.2.2) (MatrixCode.lit 4)))
    (MatrixCode.eq (MatrixCode.var q.2.2.1) (rawLayout.succCall (MatrixCode.var q.2.2.2)))) := by
  have u : Primrec (fun q : G => q.2.1) := Primrec.fst.comp Primrec.snd
  have v : Primrec (fun q : G => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have a : Primrec (fun q : G => MatrixCode.var q.2.2.2) := varProgram.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have call : Primrec (fun q : G => rawLayout.succCall (MatrixCode.var q.2.2.2)) :=
    unaryProgram.comp (Primrec.const _) a
  exact andProgram.comp (eqProgram.comp (varProgram.comp u) (addProgram.comp a (Primrec.const (MatrixCode.lit 4))))
    (eqProgram.comp (varProgram.comp v) call)

theorem gateProgram : Primrec (fun q : List Nat×Nat×Nat×Nat => fGate rawLayout q.1 q.2.1 q.2.2.1 q.2.2.2) :=
  Primrec.list_foldr (Primrec.list_map (Primrec.const (List.range 4)) gateCell) gateHigh
    (orProgram.comp Primrec.snd).to₂

/-- A reverse literal fold implements the same consecutive-position rows.
No ordinal evaluation is supplied here; the values already came from J. -/
private theorem indexedFoldProgram {α : Type} [Primcodable α] (base : Nat)
    (combine : α→Nat→Nat→Nat→Nat)
    (hc : Primrec (fun q : α×Nat×Nat×Nat => combine q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    Primrec (fun q : α×Nat×List Nat =>
      (q.2.2.foldr (fun (x : Nat) (s : Nat×Nat) => (s.1-1,combine q.1 (s.1-1) x s.2)) (q.2.1+q.2.2.length,base)).2) := by
  let P := α×Nat×List Nat
  let X := P×Nat×Nat×Nat
  have xs : Primrec (fun q : P => q.2.2) := Primrec.snd.comp Primrec.snd
  have z : Primrec (fun q : P => (q.2.1+q.2.2.length,base)) :=
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.list_length.comp xs)).pair
      (Primrec.const base)
  have pos : Primrec (fun q : X => q.2.2.1-1) :=
    Primrec.nat_sub.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 1)
  have c : Primrec (fun q : X => combine q.1.1 (q.2.2.1-1) q.2.1 q.2.2.2) :=
    hc.comp ((Primrec.fst.comp Primrec.fst).pair (pos.pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
  exact Primrec.snd.comp (Primrec.list_foldr xs z ((pos.pair c).to₂))

private def indexedList {α : Type} (base : Nat) (combine : α→Nat→Nat→Nat→Nat) (q : α) :
    Nat → List Nat → Nat
  | _,[] => base
  | i,x::xs => combine q i x (indexedList base combine q (i+1) xs)

private theorem indexedCal {α : Type} (base : Nat) (combine : α→Nat→Nat→Nat→Nat) (q : α)
    (i : Nat) (xs : List Nat) :
    (xs.foldr (fun (x : Nat) (s : Nat×Nat) => (s.1-1,combine q (s.1-1) x s.2))
      (i+xs.length,base))=(i,indexedList base combine q i xs) := by
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    simp only [List.length_cons,List.foldr_cons,indexedList]
    rw [show i+(xs.length+1)=(i+1)+xs.length by omega,ih (i+1),Nat.add_sub_cancel]

private theorem indexedProgram {α : Type} [Primcodable α] (base : Nat) (combine : α→Nat→Nat→Nat→Nat)
    (h : Primrec (fun q : α×Nat×Nat×Nat => combine q.1 q.2.1 q.2.2.1 q.2.2.2)) :
    Primrec (fun q : α×Nat×List Nat => indexedList base combine q.1 q.2.1 q.2.2) :=
  (indexedFoldProgram base combine h).of_eq (fun q => congrArg Prod.snd (indexedCal base combine q.1 q.2.1 q.2.2))

private def prefixCell (endpoints : Nat×Nat) (i x rest : Nat) : Nat :=
  MatrixCode.either (MatrixCode.both (MatrixCode.eq (MatrixCode.var endpoints.1) (MatrixCode.lit i))
    (MatrixCode.eq (MatrixCode.var endpoints.2) (MatrixCode.lit x))) rest

private theorem prefixCellProgram : Primrec (fun q : (Nat×Nat)×Nat×Nat×Nat =>
    prefixCell q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  let P := (Nat×Nat)×Nat×Nat×Nat
  have t : Primrec (fun q : P => q.1.1) := Primrec.fst.comp Primrec.fst
  have y : Primrec (fun q : P => q.1.2) := Primrec.snd.comp Primrec.fst
  have i : Primrec (fun q : P => q.2.1) := Primrec.fst.comp Primrec.snd
  have j : Primrec (fun q : P => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have h := andProgram.comp (eqProgram.comp (varProgram.comp t) (litProgram.comp i))
      (eqProgram.comp (varProgram.comp y) (litProgram.comp j))
  exact orProgram.comp h (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem prefixProgram : Primrec (fun q : (Nat×Nat)×Nat×List Nat => prefixBody rawLayout q.1.1 q.1.2 q.2.1 q.2.2) := by
  apply (indexedProgram 1 prefixCell prefixCellProgram).of_eq
  rintro ⟨ends,i,xs⟩
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih =>
    simp only [indexedList,prefixBody,prefixCell,rawLayout]
    rw [ih (i+1)]

theorem pinProgram : Primrec₂ pinCode := by
  let combine : Nat → Nat → Nat → Nat → Nat := fun _ i x rest =>
    MatrixCode.both (MatrixCode.eq (MatrixCode.var i) (MatrixCode.lit x)) rest
  have h : Primrec (fun q : Nat×Nat×Nat×Nat => combine q.1 q.2.1 q.2.2.1 q.2.2.2) :=
    andProgram.comp (eqProgram.comp (varProgram.comp (Primrec.fst.comp Primrec.snd))
      (litProgram.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  apply ((indexedProgram 0 combine h).comp ((Primrec.const 0).pair Primrec.id)).of_eq
  rintro ⟨i,xs⟩
  induction xs generalizing i with
  | nil => rfl
  | cons x xs ih => simp [indexedList,pinCode,combine,ih]

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
