module

public import LogicLineages.PersistentMarking.NumberedWindowLexicalProgramTargets
import LogicLineages.PersistentMarking.NumberedWindowAnnotationProgramProof
import LogicLineages.PersistentMarking.NumberedWindowDirectListsPrimrec

public section
namespace LogicLineages.PersistentMarking.NumberedWindowLexicalRequirementPrograms
open NumberedWindowLexicalAlgorithm

theorem eqBool {α} [Primcodable α] [DecidableEq α] [BEq α] [LawfulBEq α] :
    Primrec₂ (fun (a b : α) => a == b) := by
  apply ((Primrec.eq : PrimrecRel (Eq : α → α → Prop)).decide).of_eq
  rintro ⟨a,b⟩
  apply Bool.eq_iff_iff.mpr
  simp

theorem slotPrim : Primrec₂ slot := (Primrec.const true).pair
  (Primrec.list_cons.comp (Primrec.fst.pair Primrec.snd) (Primrec.const []))
theorem joinPrim : Primrec₂ join := (Primrec.and.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
  (Primrec.list_append.comp (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
theorem restrictPrim : Primrec₂ restrict :=
  (Primrec.and.comp Primrec.fst (Primrec.fst.comp Primrec.snd)).pair (Primrec.snd.comp Primrec.snd)

private def dischargeOne (t : Nat) (p : Nat × Nat) (r : Requirement) :=
  if p.1 = 0 then restrict (p.2 == t) r else join (slot p.1.pred p.2) r

private theorem dischargePrim : Primrec₂ discharge := by
  let E := Nat × List (Nat × Nat)
  let P := E × (Nat × Nat) × Requirement
  have i : Primrec (fun p : P => p.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have u : Primrec (fun p : P => p.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have t : Primrec (fun p : P => p.1.1) := Primrec.fst.comp Primrec.fst
  have r : Primrec (fun p : P => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : P => dischargeOne p.1.1 p.2.1 p.2.2) :=
    Primrec.ite (Primrec.eq.comp i (Primrec.const 0))
      (restrictPrim.comp (eqBool.comp u t) r) (joinPrim.comp (slotPrim.comp (Primrec.pred.comp i) u) r)
  apply (Primrec.list_foldr (Primrec.snd : Primrec (Prod.snd : E → _)) (Primrec.const empty) step.to₂).of_eq
  rintro ⟨t,rs⟩
  induction rs with
  | nil => rfl
  | cons p rs ih =>
    rcases p with ⟨_ | i,u⟩ <;> simp [dischargeOne,discharge,ih]

theorem binderPrim : Primrec₂ binder := restrictPrim.comp (Primrec.fst.comp Primrec.snd)
  (dischargePrim.comp Primrec.fst (Primrec.snd.comp Primrec.snd))

theorem holdsPrim : Primrec₂ (fun (ctx : List Nat) r => holds (fun i => ctx[i]?) r) := by
  have test : Primrec₂ (fun (p : Nat × Nat) (ctx : List Nat) => ctx[p.1]? == some p.2) :=
    eqBool.comp (Primrec.list_getElem?.comp Primrec.snd (Primrec.fst.comp Primrec.fst)) (Primrec.option_some.comp (Primrec.snd.comp Primrec.fst))
  exact Primrec.and.comp (Primrec.fst.comp Primrec.snd)
    ((NumberedWindowDirectListsPrimrec.allWith test).comp (Primrec.snd.comp Primrec.snd) Primrec.fst)
end LogicLineages.PersistentMarking.NumberedWindowLexicalRequirementPrograms
