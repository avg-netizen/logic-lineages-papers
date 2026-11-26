module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.BlockFormulaSubstitutionCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
open TiedLinearCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem variableItem_primitive : Primrec variableItem :=
  (Primrec.const 0).pair (Primrec.id.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))
#print axioms variableItem_primitive

theorem rawToken_primitive : Primrec rawToken :=
  (Primrec.const 1).pair (Primrec.encode.comp variableItem_primitive)
#print axioms rawToken_primitive

theorem rowTokens_primitive : Primrec rowTokens := by
  have he : Primrec (fun p : BlockRowSubstitutionCode.RowData × BlockRowSubstitutionCode.EntryData =>
      ((1 : Nat), Encodable.encode p.2.2)) :=
    (Primrec.const 1).pair (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))
  have hm := Primrec.list_map (Primrec.snd : Primrec (fun r : BlockRowSubstitutionCode.RowData => r.2)) he.to₂
  exact Primrec.list_append.comp
    (Primrec.list_cons.comp ((Primrec.const 0).pair (Primrec.fst.comp Primrec.fst))
      (Primrec.list_cons.comp ((Primrec.const 0).pair (Primrec.snd.comp Primrec.fst)) (Primrec.const []))) hm
#print axioms rowTokens_primitive

theorem tokens_primitive : Primrec tokens := by
  have hr : Primrec (fun p : Nat × Nat =>
      rowTokens (BlockFormulaSubstitutionCode.decodeAtom p.2).2.2) :=
    rowTokens_primitive.comp (Primrec.snd.comp (Primrec.snd.comp
      (BlockFormulaSubstitutionCodeProof.decodeAtom_primitive.comp Primrec.snd)))
  exact Primrec.list_flatMap LinearRowsCodeProof.atoms_primitive hr.to₂
#print axioms tokens_primitive

theorem tokenName_primitive : Primrec (fun p : (List TokenData × Nat) × TokenData =>
    tokenName p.1.1 p.1.2 p.2) := by
  let C := (List TokenData × Nat) × TokenData
  have he : Primrec (fun p : C × TokenData => decide (p.2 = p.1.2)) :=
    (Primrec.eq.comp Primrec.snd (Primrec.snd.comp Primrec.fst)).decide
  have hi : Primrec (fun p : C => p.1.1.idxOf p.2) := by
    apply (Primrec.list_findIdx (Primrec.fst.comp Primrec.fst) he.to₂).of_eq
    intro p
    simp only [List.idxOf, Bool.beq_eq_decide_eq]
  exact Primrec.ite (Primrec.eq.comp Primrec.snd
    (rawToken_primitive.comp (Primrec.snd.comp Primrec.fst))) (Primrec.const 0)
    (Primrec.nat_add.comp hi (Primrec.const 1))
#print axioms tokenName_primitive
attribute [local irreducible] tokenName

theorem tokenOfName_primitive : Primrec (fun p : (List TokenData × Nat) × Nat =>
    tokenOfName p.1.1 p.1.2 p.2) :=
  Primrec.ite (Primrec.eq.comp Primrec.snd (Primrec.const 0))
    (rawToken_primitive.comp (Primrec.snd.comp Primrec.fst))
    (Primrec.option_getD.comp
      (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)))
      (Primrec.const (0, WindowCode.numeral 0)))
#print axioms tokenOfName_primitive
attribute [local irreducible] tokenOfName

theorem liftRow_primitive : Primrec (fun p : (List TokenData × Nat) × BlockRowSubstitutionCode.RowData =>
    liftRow p.1.1 p.1.2 p.2) := by
  let C := (List TokenData × Nat) × BlockRowSubstitutionCode.RowData
  have hp : Primrec (fun p : C => variableItem (tokenName p.1.1 p.1.2 (0, p.2.1.1))) :=
    variableItem_primitive.comp (tokenName_primitive.comp
      (Primrec.fst.pair ((Primrec.const 0).pair (Primrec.fst.comp (Primrec.fst.comp Primrec.snd)))))
  have hn : Primrec (fun p : C => variableItem (tokenName p.1.1 p.1.2 (0, p.2.1.2))) :=
    variableItem_primitive.comp (tokenName_primitive.comp
      (Primrec.fst.pair ((Primrec.const 0).pair (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))))
  have he : Primrec (fun p : C × BlockRowSubstitutionCode.EntryData =>
      (p.2.1, variableItem (tokenName p.1.1.1 p.1.1.2 (1, Encodable.encode p.2.2)))) :=
    (Primrec.fst.comp Primrec.snd).pair
      (variableItem_primitive.comp (tokenName_primitive.comp
        ((Primrec.fst.comp Primrec.fst).pair
          ((Primrec.const 1).pair (Primrec.encode.comp (Primrec.snd.comp Primrec.snd))))))
  exact (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair hp)
      (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair hn)
        (Primrec.list_map (Primrec.snd.comp Primrec.snd) he.to₂)))
#print axioms liftRow_primitive
attribute [local irreducible] liftRow

theorem liftAtom_primitive : Primrec (fun p : (List TokenData × Nat) × BlockFormulaSubstitutionCode.AtomData =>
    liftAtom p.1.1 p.1.2 p.2) :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (liftRow_primitive.comp (Primrec.fst.pair (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))
#print axioms liftAtom_primitive
attribute [local irreducible] liftAtom

theorem liftEncodedAtom_primitive : Primrec (fun p : (List TokenData × Nat) × Nat =>
    liftEncodedAtom p.1.1 p.1.2 p.2) :=
  Primrec.encode.comp (liftAtom_primitive.comp
    (Primrec.fst.pair (BlockFormulaSubstitutionCodeProof.decodeAtom_primitive.comp Primrec.snd)))
#print axioms liftEncodedAtom_primitive
attribute [local irreducible] liftEncodedAtom

theorem liftFormula_computable : Computable (fun p : AdapterInput => liftFormula p.1 p.2.1 p.2.2) := by
  have hm : Computable (fun p : (List TokenData × Nat) × Nat =>
      LinearRows.Code.mapAtoms (liftEncodedAtom p.1.1 p.1.2) p.2) :=
    ComputableMapAtomsProof.actualJointMapProgram (List TokenData × Nat)
      (fun args code => liftEncodedAtom args.1 args.2 code) liftEncodedAtom_primitive.to_comp
  exact hm.comp ((Computable.fst.pair (Computable.fst.comp Computable.snd)).pair
    (Computable.snd.comp Computable.snd))
#print axioms liftFormula_computable

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProof
