module
public import LogicLineages.PermittedControl.OriginalPrintedCircuitNumericReadTargets
import LogicLineages.PermittedControl.TerminalEntryScanGuardProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.LayeredComparison.IntegerAlgorithmsProof
import Mathlib.Computability.Primrec.List

@[expose] public section
namespace LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRead
open OrdinalComparison FieldComparison
open OrdinalComparison.LayeredComparison.IntegerAlgorithms.Proof
open NaturalAffineGateGraph (Expression)

theorem tagPrimitive : Primrec tag := Primrec.fst.comp Primrec.snd

theorem sourcePrimitive : Primrec source := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

private theorem dataPrimitive : Primrec (fun p : Args => p.2.2.2.2) :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))

theorem payloadPrimitive : Primrec payload := Primrec.fst.comp dataPrimitive

theorem expressionPrimitive : Primrec expression := Primrec.snd.comp dataPrimitive

theorem inputPrimitive : Primrec inputValue :=
  (Primrec.list_getD 0).comp Primrec.fst sourcePrimitive

theorem sameTag (n : Nat) : Primrec (fun p : Args => decide (tag p = n)) :=
  (Primrec.eq.comp tagPrimitive (Primrec.const n)).decide

theorem hitPrimitive : Primrec (fun n : Nat => n + 4) :=
  Primrec.nat_add.comp Primrec.id (Primrec.const 4)

private theorem packOption (noneCode : Nat) :
    Primrec (fun r : Option Nat => r.casesOn noneCode (fun n => n+4)) := by
  let A := Option Nat × Nat
  have someCode : Primrec (fun p : A => p.2 + 4) := hitPrimitive.comp Primrec.snd
  exact Primrec.option_casesOn Primrec.id (Primrec.const noneCode) someCode.to₂

theorem packBasePrimitive : Primrec packBase :=
  (packOption 1).of_eq (fun p => by cases p <;> rfl)

theorem packFieldPrimitive : Primrec packField := by
  let A := ClosedNaturalFieldResult × Option Nat
  have someCode : Primrec (fun p : A => p.2.casesOn 3 (fun n => n+4)) :=
    (packOption 3).comp Primrec.snd
  exact (Primrec.option_casesOn Primrec.id (Primrec.const 2) someCode.to₂).of_eq
    (fun p => by rcases p with - | q <;> rfl)

theorem identityGuardPrimitive : Primrec identityGuard := by
  have htarget : Primrec (fun p : Nat × Nat => terminalScanGuard (p.1,p.1)) :=
    terminalEntryScanGuardExact.1.comp (Primrec.fst.pair Primrec.fst)
  have hnorm : Primrec (fun p : Nat × Nat => rawNormCode p.1) :=
    (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp Primrec.fst
  exact Primrec.and.comp htarget ((Primrec.nat_le.comp hnorm Primrec.snd).decide)

theorem identityValueCodePrimitive : Primrec identityValueCode := by
  let A := Nat × Nat × Nat
  have args : Primrec (fun p : A => (p.1,p.2.1)) := Primrec.fst.pair (Primrec.fst.comp Primrec.snd)
  have value : Primrec (fun p : A => p.2.2 + 4) :=
    hitPrimitive.comp (Primrec.snd.comp Primrec.snd)
  exact (Primrec.cond (identityGuardPrimitive.comp args) value (Primrec.const 2)).of_eq
    (fun p => by cases h : identityGuard (p.1,p.2.1) <;> simp [identityValueCode,h])

theorem parserPrimitive : Primrec parser := by
  have terms : Primrec (fun p : Args => (expression p).2) := Primrec.snd.comp expressionPrimitive
  have len : Primrec (fun p : Args => p.1.length) := Primrec.list_length.comp Primrec.fst
  let Stage := Args × ((Int × Nat) × Bool)
  have ti : Primrec (fun p : Stage => p.2.1.2) :=
    Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have next : Primrec (fun p : Stage => decide (p.2.1.2 < p.1.1.length) && p.2.2) :=
    Primrec.and.comp ((Primrec.nat_lt.comp ti (len.comp Primrec.fst)).decide)
      (Primrec.snd.comp Primrec.snd)
  have checked : Primrec (fun p : Args =>
      (expression p).2.all (fun t => decide (t.2 < p.1.length))) := by
    apply (Primrec.list_foldr terms (Primrec.const true) next.to₂).of_eq
    intro p
    generalize (expression p).2 = ts
    induction ts with
    | nil => rfl
    | cons t ts ih => simp [List.foldr_cons,List.all_cons,ih]
  have unary := (Primrec.nat_lt.comp sourcePrimitive len).decide
  have tags := (Primrec.nat_le.comp tagPrimitive (Primrec.const 6)).decide
  exact Primrec.and.comp tags
    (Primrec.ite (Primrec.eq.comp tagPrimitive (Primrec.const 0)) checked unary)

theorem signedBankPrimitive : Primrec signedBank := by
  let Stage := Args × ((Int × Nat) × Int)
  have terms : Primrec (fun p : Args => (expression p).2) := Primrec.snd.comp expressionPrimitive
  have const : Primrec (fun p : Args => (expression p).1) := Primrec.fst.comp expressionPrimitive
  have t : Primrec (fun p : Stage => p.2.1) := Primrec.fst.comp Primrec.snd
  have coeff : Primrec (fun p : Stage => p.2.1.1) := Primrec.fst.comp t
  have name : Primrec (fun p : Stage => p.2.1.2) := Primrec.snd.comp t
  have values : Primrec (fun p : Stage => p.1.1) := Primrec.fst.comp Primrec.fst
  have value := ofNat_primitive.comp ((Primrec.list_getD 0).comp values name)
  have acc : Primrec (fun p : Stage => p.2.2) := Primrec.snd.comp Primrec.snd
  have step : Primrec (fun p : Stage => p.2.1.1 * (bank p.1.1 p.2.1.2 : Int) + p.2.2) :=
    add_primitive.comp (mul_primitive.comp coeff value) acc
  exact add_primitive.comp const (Primrec.list_foldr terms (Primrec.const (0 : Int)) step.to₂)

theorem packAffinePrimitive : Primrec packAffine :=
  Primrec.ite (Primrec.eq.comp sign_primitive (Primrec.const (-1 : Int)))
    (Primrec.const 1) (hitPrimitive.comp abs_primitive)

end LogicLineages.PermittedControl.OriginalPrintedCircuitNumericRead
