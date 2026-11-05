module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceRowsCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeRecursionProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof
open SourceBooleanPrograms
attribute [local irreducible] Nat.sqrt Nat.unpair LinearRows.Code.decodeAtom

theorem shiftItem_primitive : Primrec₂ Code.shiftItem :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.nat_add.comp Primrec.fst (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))).pair
      ((Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

theorem shiftRow_primitive : Primrec₂ Code.shiftRow := by
  have hs : Primrec (fun p : (Nat × NormalForm.Code.RowData) × (Int × NormalForm.Code.ItemData) =>
      (p.2.1, Code.shiftItem p.1.1 p.2.2)) :=
    (Primrec.fst.comp Primrec.snd).pair
      (shiftItem_primitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.fst.comp Primrec.snd).pair
    (Primrec.list_map (Primrec.snd.comp Primrec.snd) hs.to₂)

theorem shiftAtom_primitive : Primrec₂ Code.shiftAtom :=
  (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (shiftRow_primitive.comp Primrec.fst (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

attribute [local irreducible] Code.shiftAtom

theorem shift_primitive : Primrec₂ Code.shift := by
  have hop : Primrec₂ (fun d a => Encodable.encode (Code.shiftAtom d (LinearRows.Code.decodeAtom a))) :=
    Primrec.encode.comp (shiftAtom_primitive.comp Primrec.fst (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd))
  exact LinearRowsCodeProof.mapAtoms_primitive hop

theorem count_primitive : Primrec Code.count :=
  Primrec.list_length.comp SourceTermGraphCodeProof.instructions_primitive

theorem binary_primitive (base tag : Nat) :
    Primrec₂ (fun a b : Nat => base * Nat.pair a b + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec₂.natPair) (Primrec.const tag)

theorem unary_primitive (base tag : Nat) : Primrec (fun a : Nat => base * a + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec.id) (Primrec.const tag)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceBooleanProgramsProof
