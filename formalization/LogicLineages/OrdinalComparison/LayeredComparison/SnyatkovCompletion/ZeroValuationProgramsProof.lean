module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ClosedLinearCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationProof
open ZeroValuation
attribute [local irreducible] Nat.sqrt Nat.unpair
attribute [local irreducible] BoundedRows.Code.itemValue LinearRows.Code.decodeAtom

private theorem integerSum_primitive : Primrec (fun xs : List Int => xs.sum) := by
  have hs : Primrec (fun p : List Int × (Int × Int) => p.2.1 + p.2.2) :=
    IntegerAlgorithms.Proof.add_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Int => xs.foldr (fun a b => a + b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const 0) hs.to₂
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, List.sum_cons, ih]

theorem projectRow_primitive : Primrec Code.projectRow := by
  let A := NormalForm.Code.RowData × (Int × NormalForm.Code.ItemData)
  have hv : Primrec (fun p : A => (BoundedRows.Code.itemValue p.2.2 0 : Int)) :=
    IntegerAlgorithms.Proof.ofNat_primitive.comp
      (BoundedRowsCodeProof.itemValue_primitive.comp (Primrec.snd.comp Primrec.snd) (Primrec.const 0))
  have hw : Primrec (fun p : A => p.2.1 * (BoundedRows.Code.itemValue p.2.2 0 : Int)) :=
    IntegerAlgorithms.Proof.mul_primitive.comp (Primrec.fst.comp Primrec.snd) hv
  exact (IntegerAlgorithms.Proof.add_primitive.comp Primrec.fst
    (integerSum_primitive.comp (Primrec.list_map Primrec.snd hw.to₂))).pair (Primrec.const [])

theorem projectAtom_primitive : Primrec Code.projectAtom :=
  Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair
    (projectRow_primitive.comp (Primrec.snd.comp Primrec.snd)))

attribute [local irreducible] Code.projectAtom

theorem project_primitive : Primrec Code.project := by
  have hop : Primrec₂ (fun (_ : Unit) a => Encodable.encode (Code.projectAtom (LinearRows.Code.decodeAtom a))) :=
    Primrec.encode.comp (projectAtom_primitive.comp (LinearRowsCodeProof.decodeAtom_primitive.comp Primrec.snd))
  exact (LinearRowsCodeProof.mapAtoms_primitive hop).comp (Primrec.const ()) Primrec.id

attribute [local irreducible] Code.project

theorem evaluate_primitive : Primrec Code.evaluate :=
  ClosedLinearProof.evaluateConstants_primitive.comp project_primitive

theorem actualNumericPrograms : ZeroValuationTargets.ActualNumericPrograms :=
  ⟨projectRow_primitive, projectAtom_primitive, project_primitive, evaluate_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.ZeroValuationProof
