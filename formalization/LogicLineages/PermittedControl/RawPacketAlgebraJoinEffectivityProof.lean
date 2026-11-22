module
public import LogicLineages.PermittedControl.RawPacketAlgebraJoinTargets
import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof

public section
namespace LogicLineages.PermittedControl.RawPacketAlgebra
open OrdinalComparison.LayeredComparison.SnyatkovCompletion
open PreparedProjection (LowerOperandCode PreparedPacketCode)

theorem shiftNamePrimitive : Primrec₂ shiftNameCode :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0)) (Primrec.const 0)
    (Primrec.nat_add.comp Primrec.fst Primrec.snd)

theorem shiftItemPrimitive : Primrec₂ shiftItemCode := by
  let A := Nat × NormalForm.Code.ItemData
  have tag : Primrec (fun q : A => q.2.1) := Primrec.fst.comp Primrec.snd
  have name : Primrec (fun q : A => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have rest : Primrec (fun q : A => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact tag.pair ((shiftNamePrimitive.comp Primrec.fst name).pair rest)

theorem shiftRowPrimitive : Primrec₂ shiftRowCode := by
  let A := Nat × NormalForm.Code.RowData
  let I := Int × NormalForm.Code.ItemData
  have g : Primrec₂ (fun (q : A) (a : I) => (a.1,shiftItemCode q.1 a.2)) :=
    (Primrec.fst.comp Primrec.snd).pair
      (shiftItemPrimitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.fst.comp Primrec.snd).pair (Primrec.list_map (Primrec.snd.comp Primrec.snd) g)

theorem shiftAtomDataPrimitive : Primrec₂ shiftAtomData := by
  let A := Nat × NormalForm.Code.AtomData
  have tag : Primrec (fun q : A => q.2.1) := Primrec.fst.comp Primrec.snd
  have modulus : Primrec (fun q : A => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have row : Primrec (fun q : A => q.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact tag.pair (modulus.pair (shiftRowPrimitive.comp Primrec.fst row))

theorem shiftAtomPrimitive : Primrec₂ shiftAtomCode :=
  Primrec.encode.comp
    (shiftAtomDataPrimitive.comp Primrec.fst
      (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd))

theorem shiftPrimitive : Primrec₂ shiftCode :=
  LinearRowsCodeProof.mapAtoms_primitive shiftAtomPrimitive

theorem tablePrimitive : Primrec tableOf :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option (List LowerOperandCode))))
    (Primrec.const [])

theorem appendPrimitive : Primrec₂ appendCode := by
  let A := PreparedPacketCode × PreparedPacketCode
  have lt : Primrec (fun q : A => tableOf q.1.1) := tablePrimitive.comp (Primrec.fst.comp Primrec.fst)
  have rt : Primrec (fun q : A => tableOf q.2.1) := tablePrimitive.comp (Primrec.fst.comp Primrec.snd)
  have bytes : Primrec (fun q : A => Encodable.encode (tableOf q.1.1 ++ tableOf q.2.1)) :=
    Primrec.encode.comp (Primrec.list_append.comp lt rt)
  have sh : Primrec (fun q : A => shiftCode (tableOf q.1.1).length q.2.2) :=
    shiftPrimitive.comp (Primrec.list_length.comp lt) (Primrec.snd.comp Primrec.snd)
  have conj : Primrec (fun q : A =>
      LinearRows.Code.conjunction q.1.2 (shiftCode (tableOf q.1.1).length q.2.2)) :=
    LinearRowsCodeProof.conjunction_primitive.comp (Primrec.snd.comp Primrec.fst) sh
  exact bytes.pair conj

theorem tuplePrimitive : Primrec tupleCode := by
  have step : Primrec (fun q : PreparedPacketCode × PreparedPacketCode => appendCode q.1 q.2) :=
    appendPrimitive
  apply (Primrec.list_foldr Primrec.id (Primrec.const unitCode) (step.comp Primrec.snd).to₂).of_eq
  intro cs
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    change appendCode c (cs.foldr (fun b s => appendCode b s) unitCode) = appendCode c (tupleCode cs)
    exact congrArg (fun b => appendCode c b) ih

theorem choicesPrimitive : Primrec choicesCode := by
  let R := List PreparedPacketCode
  let S := List (List PreparedPacketCode)
  have inner : Primrec₂ (fun (q : R × S) (c : PreparedPacketCode) => q.2.map (List.cons c)) :=
    Primrec.list_map (Primrec.snd.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have step : Primrec (fun q : R × S => q.1.flatMap (fun c => q.2.map (List.cons c))) :=
    Primrec.list_flatMap Primrec.fst inner
  apply (Primrec.list_foldr Primrec.id (Primrec.const [[]]) (step.comp Primrec.snd).to₂).of_eq
  intro rows
  induction rows with
  | nil => rfl
  | cons row rows ih =>
    change row.flatMap (fun c =>
        (rows.foldr (fun b s => b.flatMap (fun c => s.map (List.cons c))) [[]]).map (List.cons c)) =
      row.flatMap (fun c => (choicesCode rows).map (List.cons c))
    exact congrArg (fun s => row.flatMap (fun c => s.map (List.cons c))) ih

theorem joinPrimitive : Primrec joinCode :=
  Primrec.list_map choicesPrimitive (tuplePrimitive.comp Primrec.snd).to₂

theorem joinEffectivity : JoinEffectivity :=
  ⟨shiftPrimitive,appendPrimitive,tuplePrimitive,choicesPrimitive,joinPrimitive⟩

#print axioms joinEffectivity

end LogicLineages.PermittedControl.RawPacketAlgebra
