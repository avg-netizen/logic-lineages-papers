module
public import LogicLineages.PermittedControl.OrdinalEndpointCodeTargets
public import LogicLineages.OrdinalComparison.RawComparisonProof

@[expose] public section
namespace LogicLineages.PermittedControl
open OrdinalComparison

 theorem ordinalNodeCode_primrec {α : Type*} [Primcodable α] {e c t : α → Nat}
    (he : Primrec e) (hc : Primrec c) (ht : Primrec t) :
    Primrec (fun p => ordinalNodeCode (e p) (c p) (t p)) :=
  Primrec.succ.comp (Primrec₂.natPair.comp he (Primrec₂.natPair.comp hc ht))

 theorem ordinalAddAuxCode_primrec : Primrec (fun p : Nat×Nat×Nat => ordinalAddAuxCode p.1 p.2.1 p.2.2) := by
  have he : Primrec (fun p : Nat×Nat×Nat => p.1) := Primrec.fst
  have hc : Primrec (fun p : Nat×Nat×Nat => p.2.1) := Primrec.fst.comp Primrec.snd
  have hz : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  have hv := Primrec.nat_sub.comp hz (Primrec.const 1)
  have hu := Primrec.unpair.comp hv
  have hzE := Primrec.fst.comp hu
  have hzCT := Primrec.unpair.comp (Primrec.snd.comp hu)
  have hzC := Primrec.fst.comp hzCT
  have hzT := Primrec.snd.comp hzCT
  have hcmp := rawComparisonPrimitiveRecursive.comp he hzE
  have hsum := Primrec.succ.comp (Primrec.nat_add.comp hc hzC)
  exact Primrec.ite (Primrec.eq.comp hz (Primrec.const 0))
    (ordinalNodeCode_primrec he hc (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hcmp (Primrec.const 0)) hz
      (Primrec.ite (Primrec.eq.comp hcmp (Primrec.const 1))
        (ordinalNodeCode_primrec he hsum hzT) (ordinalNodeCode_primrec he hc hz)))

 theorem ordinalAddCodeStep_primrec : Primrec₂ ordinalAddCodeStep := by
  have hn : Primrec (fun p : Nat×List Nat => p.1) := Primrec.fst
  have ht : Primrec (fun p : Nat×List Nat => p.2) := Primrec.snd
  have hab := Primrec.unpair.comp hn
  have ha := Primrec.fst.comp hab
  have hb := Primrec.snd.comp hab
  have hu := Primrec.unpair.comp (Primrec.nat_sub.comp ha (Primrec.const 1))
  have he := Primrec.fst.comp hu
  have hct := Primrec.unpair.comp (Primrec.snd.comp hu)
  have hc := Primrec.fst.comp hct
  have htail := Primrec.snd.comp hct
  have hrecursive := (Primrec.list_getD 0).comp ht (Primrec₂.natPair.comp htail hb)
  exact Primrec.ite (Primrec.eq.comp ha (Primrec.const 0)) hb
    (ordinalAddAuxCode_primrec.comp (he.pair (hc.pair hrecursive)))

 theorem ordinalSubCodeStep_primrec : Primrec₂ ordinalSubCodeStep := by
  have hn : Primrec (fun p : Nat×List Nat => p.1) := Primrec.fst
  have ht : Primrec (fun p : Nat×List Nat => p.2) := Primrec.snd
  have hab := Primrec.unpair.comp hn
  have ha := Primrec.fst.comp hab
  have hb := Primrec.snd.comp hab
  have hu := Primrec.unpair.comp (Primrec.nat_sub.comp ha (Primrec.const 1))
  have hv := Primrec.unpair.comp (Primrec.nat_sub.comp hb (Primrec.const 1))
  have hea := Primrec.fst.comp hu
  have heb := Primrec.fst.comp hv
  have hct := Primrec.unpair.comp (Primrec.snd.comp hu)
  have hdt := Primrec.unpair.comp (Primrec.snd.comp hv)
  have hc := Primrec.fst.comp hct
  have hd := Primrec.fst.comp hdt
  have hta := Primrec.snd.comp hct
  have htb := Primrec.snd.comp hdt
  have hcmp := rawComparisonPrimitiveRecursive.comp hea heb
  have hrecursive := (Primrec.list_getD 0).comp ht (Primrec₂.natPair.comp hta htb)
  have hdiff := Primrec.nat_sub.comp (Primrec.nat_sub.comp hc hd) (Primrec.const 1)
  exact Primrec.ite (Primrec.eq.comp ha (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.eq.comp hb (Primrec.const 0)) ha
      (Primrec.ite (Primrec.eq.comp hcmp (Primrec.const 0)) (Primrec.const 0)
        (Primrec.ite (Primrec.eq.comp hcmp (Primrec.const 2)) ha
          (Primrec.ite (Primrec.eq.comp hc hd) hrecursive
            (Primrec.ite (Primrec.nat_lt.comp hd hc)
              (ordinalNodeCode_primrec hea hdiff hta) (Primrec.const 0))))))

 theorem ordinalAddCodeEffective : Primrec₂ ordinalAddCode := by
  let step : Nat → List Nat → List Nat := fun n table => table ++ [ordinalAddCodeStep n table]
  have hs : Primrec₂ step := Primrec.list_concat.comp Primrec.snd ordinalAddCodeStep_primrec
  have ht : Primrec ordinalAddCodeTable := (Primrec.nat_rec₁ [] hs).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => change step n _ = _; rw [ih]; rfl)
  exact (Primrec.list_getD 0).comp (ht.comp (Primrec.succ.comp Primrec₂.natPair)) Primrec₂.natPair

 theorem ordinalSubCodeEffective : Primrec₂ ordinalSubCode := by
  let step : Nat → List Nat → List Nat := fun n table => table ++ [ordinalSubCodeStep n table]
  have hs : Primrec₂ step := Primrec.list_concat.comp Primrec.snd ordinalSubCodeStep_primrec
  have ht : Primrec ordinalSubCodeTable := (Primrec.nat_rec₁ [] hs).of_eq (by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => change step n _ = _; rw [ih]; rfl)
  exact (Primrec.list_getD 0).comp (ht.comp (Primrec.succ.comp Primrec₂.natPair)) Primrec₂.natPair

 theorem ordinalEndpointCodeEffective : Targets.OrdinalEndpointCodeEffective :=
  ⟨ordinalAddCodeEffective,ordinalSubCodeEffective⟩

end LogicLineages.PermittedControl
