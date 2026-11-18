module
public import LogicLineages.StandardControlCurrent.InactiveEliminationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeCalibrationProof
@[expose] public section
namespace LogicLineages.StandardControlCurrent.InactiveEliminationProgramsProof
open OrdinalComparison LayeredComparison.SnyatkovCompletion NormalForm InactiveElimination

abbrev Item := Int × NormalForm.Code.ItemData
private theorem nonzero_primitive : Primrec (fun a : Item => a.1 != 0) :=
  Primrec.not.comp (Primrec.beq.comp Primrec.fst (Primrec.const 0))
private theorem filter_primitive : Primrec (fun as : List Item => as.filter (fun a => a.1 != 0)) := by
  have hs : Primrec (fun q : List Item × (Item × List Item) =>
      bif q.2.1.1 != 0 then q.2.1 :: q.2.2 else q.2.2) :=
    Primrec.cond (nonzero_primitive.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun as : List Item => as.foldr
      (fun b bs => bif b.1 != 0 then b :: bs else bs) []) :=
    Primrec.list_foldr Primrec.id (Primrec.const []) hs.to₂
  apply hf.of_eq
  intro as
  induction as with
  | nil => rfl
  | cons a as ih =>
      simp only [List.foldr_cons,List.filter_cons,ih]
      cases h : (a.1 != 0) <;> simp [h]

private theorem clean_data_primitive : Primrec (fun a : NormalForm.Code.AtomData =>
    (a.1,a.2.1,a.2.2.1,a.2.2.2.filter (fun z => z.1 != 0))) :=
  Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (filter_primitive.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))))

theorem cleanAtom_primitive : Primrec Code.cleanAtom :=
  Primrec.encode.comp (clean_data_primitive.comp LinearRowsCodeProof.decodeAtom_primitive)

theorem clean_primitive : Primrec Code.clean :=
  (LinearRowsCodeProof.mapAtoms_primitive
    (cleanAtom_primitive.comp (Primrec.snd : Primrec (fun q : Unit × Nat => q.2))).to₂).comp
      (Primrec.const ()) Primrec.id

theorem eliminate_primitive : Primrec₂ Code.eliminate :=
  LinearRowsCodeProof.eliminate_primitive.comp Primrec.fst (clean_primitive.comp Primrec.snd)

theorem cleanAtom_calibration (a : Atom) :
    Code.cleanAtom (Encodable.encode a.data) = Encodable.encode (cleanAtom a).data := by
  have hd : LinearRows.Code.decodeAtom (Encodable.encode a.data) = a.data := by
    simp only [LinearRows.Code.decodeAtom,Encodable.encodek,Option.getD_some]
  unfold Code.cleanAtom
  rw [hd]
  cases a <;> simp only [cleanAtom,cleanRow,Atom.data,rowData,List.filter_map,Function.comp_def]

private theorem map_step (op : Nat → Nat) (payload tag : Nat) (ht : tag < 6) :
    LinearRows.Code.mapAtoms op (6*payload+tag) =
      if tag=0 then 0 else if tag=1 then 1 else if tag=2 then 6*op payload+2
      else if tag=3 then 6*LinearRows.Code.mapAtoms op payload+3
      else 6*Nat.pair (LinearRows.Code.mapAtoms op payload.unpair.1)
        (LinearRows.Code.mapAtoms op payload.unpair.2)+tag := by
  have hm : (6*payload+tag)%6=tag := by omega
  have hd : (6*payload+tag)/6=payload := by omega
  rw [LinearRows.Code.mapAtoms,hm,hd]

theorem clean_calibration (p : Formula) : Code.clean p.encode=(clean p).encode := by
  change LinearRows.Code.mapAtoms Code.cleanAtom p.encode = _
  induction p with
  | truth => simpa [Formula.encode,clean] using map_step Code.cleanAtom 0 0 (by decide)
  | falsity => simpa [Formula.encode,clean] using map_step Code.cleanAtom 0 1 (by decide)
  | atom a =>
      simpa [Formula.encode,clean,cleanAtom_calibration] using
        map_step Code.cleanAtom (Encodable.encode a.data) 2 (by decide)
  | negative p hp =>
      simpa [Formula.encode,clean,hp] using map_step Code.cleanAtom p.encode 3 (by decide)
  | conjunction p q hp hq =>
      simpa [Formula.encode,clean,Nat.unpair_pair,hp,hq] using
        map_step Code.cleanAtom (Nat.pair p.encode q.encode) 4 (by decide)
  | disjunction p q hp hq =>
      simpa [Formula.encode,clean,Nat.unpair_pair,hp,hq] using
        map_step Code.cleanAtom (Nat.pair p.encode q.encode) 5 (by decide)

theorem eliminate_calibration (i : Nat) (p : Formula) :
    Code.eliminate i p.encode=(eliminate i p).encode := by
  rw [Code.eliminate,clean_calibration,LinearRowsCodeProof.eliminate_calibration]
  rfl

theorem programs : InactiveEliminationTargets.Programs :=
  ⟨clean_primitive,eliminate_primitive,clean_calibration,eliminate_calibration⟩
end LogicLineages.StandardControlCurrent.InactiveEliminationProgramsProof
