module
public import LogicLineages.PermittedControl.RankResidueChoicesTargets

@[expose] public section
namespace LogicLineages.PermittedControl.RankResidueChoices

theorem namedSlotsPrimitive : Primrec namedSlots := by
  let Args := List Nat × Nat
  have index : Primrec (Prod.snd : Args → Nat) := Primrec.snd
  have rank : Primrec (fun p : Args => p.1[p.2]?.getD 0) :=
    Primrec.option_getD.comp (Primrec.list_getElem?.comp Primrec.fst index) (Primrec.const 0)
  exact Primrec.list_map (Primrec.list_range.comp Primrec.list_length)
    ((Primrec.succ.comp index).pair rank).to₂

private theorem extendPrimitive : Primrec (fun p : Nat × Slot × List Cell => extend p.1 p.2.1 p.2.2) := by
  let Args := Nat × Slot × List Cell
  let DigitArgs := Args × Nat
  let Input := DigitArgs × Cell
  have slot : Primrec (fun p : Input => p.1.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
  have digit : Primrec (fun p : Input => (p.1.1.2.1.1,p.1.1.2.1.2,p.1.2)) :=
    (Primrec.fst.comp slot).pair
      ((Primrec.snd.comp slot).pair (Primrec.snd.comp Primrec.fst))
  have old : Primrec (fun p : DigitArgs => p.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have extendBy : Primrec₂ (fun (p : Args) j => p.2.2.map (fun cell => (p.2.1.1,p.2.1.2,j) :: cell)) :=
    (Primrec.list_map old (Primrec.list_cons.comp digit Primrec.snd).to₂).to₂
  have indices : Primrec (fun p : Args => List.range (2*p.1)) :=
    Primrec.list_range.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst)
  exact Primrec.list_flatMap indices extendBy

theorem choicesPrimitive : Primrec₂ choices := by
  let Args := Nat × List Slot
  let Step := Args × (Slot × List Cell)
  have m : Primrec (fun p : Step => p.1.1) := Primrec.fst.comp Primrec.fst
  have state : Primrec (Prod.snd : Step → Slot × List Cell) := Primrec.snd
  have extendBy := extendPrimitive.comp (m.pair state)
  exact (Primrec.list_foldr (Primrec.snd : Primrec (Prod.snd : Args → List Slot))
    (Primrec.const [[]]) extendBy.to₂).to₂

end LogicLineages.PermittedControl.RankResidueChoices
