module
public import LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Targets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Proof
open PolynomialGraphCompletion LayeredComparison.SnyatkovCompletion
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem tokenName_primitive : Primrec₂ tokenName :=
  Primrec.ite
    (Primrec.eq.comp Primrec.snd (Primrec.fst.pair (Primrec.const ([] : Word))))
    (Primrec.const 0) (Primrec.succ.comp (Primrec.encode.comp Primrec.snd))

theorem tokenOfName_primitive : Primrec₂ tokenOfName := by
  have hn : Primrec (fun p : Nat × Nat => p.2 - 1) :=
    Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  have hd : Primrec (fun p : Nat × Nat =>
      ((Encodable.decode (p.2 - 1) : Option Token).getD (0, []))) :=
    Primrec.option_getD.comp (Primrec.decode.comp hn) (Primrec.const (0, []))
  exact Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (Primrec.fst.pair (Primrec.const ([] : Word))) hd

attribute [local irreducible] tokenName tokenOfName

theorem decodeAtom_primitive : Primrec Code.decodeAtom :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option Code.AtomData)))
    (Primrec.const (0, 0, (0 : Int), []))

theorem liftRow_primitive : Primrec₂ Code.liftRow := by
  let A := Nat × Row
  let I := Int × Token
  have hx : Primrec (fun p : A × I => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : A × I => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : A × I => p.2.2) := Primrec.snd.comp Primrec.snd
  have hn : Primrec (fun p : A × I => tokenName p.1.1 p.2.2) :=
    tokenName_primitive.comp hx ht
  have hi : Primrec (fun p : A × I =>
      (p.2.1, (0, tokenName p.1.1 p.2.2, (0 : Int), (0 : Int)))) :=
    hw.pair ((Primrec.const 0).pair (hn.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int)))))
  have hs : Primrec (fun p : A => p.2.2.map
      (fun a => (a.1, (0, tokenName p.1 a.2, (0 : Int), (0 : Int))))) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) hi.to₂
  exact (Primrec.fst.comp Primrec.snd).pair hs

theorem lowerItem_primitive : Primrec₂ Code.lowerItem := by
  let A := Nat × NormalForm.Code.ItemData
  have htag : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun p : A => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp htag (Primrec.const 0))
    (tokenOfName_primitive.comp Primrec.fst hn) (Primrec.const (0, []))

theorem lowerRow_primitive : Primrec₂ Code.lowerRow := by
  let A := Nat × NormalForm.Code.RowData
  let I := Int × NormalForm.Code.ItemData
  have hx : Primrec (fun p : A × I => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : A × I => p.2.1) := Primrec.fst.comp Primrec.snd
  have ht : Primrec (fun p : A × I => p.2.2) := Primrec.snd.comp Primrec.snd
  have hi : Primrec (fun p : A × I => (p.2.1, Code.lowerItem p.1.1 p.2.2)) :=
    hw.pair (lowerItem_primitive.comp hx ht)
  have hs : Primrec (fun p : A =>
      p.2.2.map (fun a => (a.1, Code.lowerItem p.1 a.2))) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) hi.to₂
  exact (Primrec.fst.comp Primrec.snd).pair hs

attribute [local irreducible] Code.decodeAtom Code.liftRow Code.lowerItem Code.lowerRow

theorem liftAtom_primitive : Primrec₂ Code.liftAtom :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (liftRow_primitive.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

theorem lowerAtom_primitive : Primrec₂ Code.lowerAtom :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (lowerRow_primitive.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

attribute [local irreducible] Code.liftAtom Code.lowerAtom

theorem liftFormula_primitive : Primrec₂ Code.liftFormula := by
  have hop : Primrec₂ (fun x a : Nat => Encodable.encode (Code.liftAtom x (Code.decodeAtom a))) :=
    Primrec.encode.comp (liftAtom_primitive.comp Primrec.fst (decodeAtom_primitive.comp Primrec.snd))
  exact LinearRowsCodeProof.mapAtoms_primitive hop

theorem lowerFormula_primitive : Primrec₂ Code.lowerFormula := by
  have hop : Primrec₂ (fun x a : Nat =>
      Encodable.encode (Code.lowerAtom x (LinearRows.Code.decodeAtom a))) :=
    Primrec.encode.comp (lowerAtom_primitive.comp Primrec.fst
      (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd))
  exact LinearRowsCodeProof.mapAtoms_primitive hop

attribute [local irreducible] Code.liftFormula Code.lowerFormula

theorem actualNumericProgram : Targets.ActualNumericProgram :=
  lowerFormula_primitive.comp Primrec.fst
    (LinearRowsCodeProof.eliminate_primitive.comp (Primrec.const 0) liftFormula_primitive)

end LogicLineages.OrdinalComparison.WordLinearDecisionCompletion.Proof
