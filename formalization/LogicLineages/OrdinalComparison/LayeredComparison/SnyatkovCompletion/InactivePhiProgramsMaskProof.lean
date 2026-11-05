module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsProof
open NormalForm InactivePhiPrograms

private theorem zip_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    (a₀ : α) (b₀ : β) : Primrec₂ (List.zip : List α → List β → List (α × β)) := by
  let A := List α × List β
  have hn : Primrec (fun p : A => min p.1.length p.2.length) :=
    Primrec.nat_min.comp (Primrec.list_length.comp Primrec.fst) (Primrec.list_length.comp Primrec.snd)
  have he : Primrec (fun p : A × Nat => (p.1.1.getD p.2 a₀, p.1.2.getD p.2 b₀)) :=
    ((Primrec.list_getD a₀).comp (Primrec.fst.comp Primrec.fst) Primrec.snd).pair
      ((Primrec.list_getD b₀).comp (Primrec.snd.comp Primrec.fst) Primrec.snd)
  have hf : Primrec (fun p : A => (List.range (min p.1.length p.2.length)).map
      (fun k => (p.1.getD k a₀, p.2.getD k b₀))) :=
    Primrec.list_map (Primrec.list_range.comp hn) he.to₂
  apply hf.of_eq
  intro p
  apply List.ext_getElem
  · simp
  · intro k hk hl
    have hmin : k < min p.1.length p.2.length := by simpa using hk
    have ha := (lt_min_iff.mp hmin).1
    have hb := (lt_min_iff.mp hmin).2
    simp only [List.getElem_map, List.getElem_range, List.getElem_zip,
      List.getD_eq_getElem?_getD, List.getElem?_eq_getElem ha, List.getElem?_eq_getElem hb,
      Option.getD_some]

theorem filterWith_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → β → Bool} (hp : Primrec₂ p) :
    Primrec₂ (fun (a : α) (xs : List β) => xs.filter (p a)) := by
  let A := α × List β
  have hs : Primrec (fun q : A × (β × List β) =>
      bif p q.1.1 q.2.1 then q.2.1 :: q.2.2 else q.2.2) :=
    Primrec.cond
      (hp.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun q : A => q.2.foldr
      (fun b s => bif p q.1 b then b :: s else s) []) :=
    Primrec.list_foldr Primrec.snd (Primrec.const []) hs.to₂
  apply hf.to₂.of_eq
  intro a xs
  induction xs with
  | nil => rfl
  | cons b xs ih =>
      simp only [List.foldr_cons, List.filter_cons, ih]
      cases h : p a b <;> simp [h]

private abbrev Item := Int × NormalForm.Code.ItemData

private theorem selectedItems_primitive (keep : Bool) :
    Primrec (fun p : NormalForm.Code.RowData × List Bool =>
      ((p.1.2.zip p.2).filter (fun a => a.2 == keep)).map Prod.fst) := by
  have hz : Primrec (fun p : NormalForm.Code.RowData × List Bool => p.1.2.zip p.2) :=
    (zip_primitive ((0 : Int), (0, 0, 0, 0)) false).comp (Primrec.snd.comp Primrec.fst) Primrec.snd
  have hp : Primrec₂ (fun (_ : Unit) (a : Item × Bool) => a.2 == keep) :=
    Primrec.beq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const keep)
  have hf := (filterWith_primitive hp).comp (Primrec.const ()) hz
  exact Primrec.list_map hf (Primrec.fst.comp Primrec.snd).to₂

private theorem keptItems_primitive :
    Primrec (fun p : NormalForm.Code.RowData × List Bool => Code.keptItems p.2 p.1.2) := by
  apply (selectedItems_primitive false).of_eq
  intro p
  unfold Code.keptItems
  apply congrArg (fun xs : List (Item × Bool) => xs.map Prod.fst)
  apply congrArg (fun f : Item × Bool → Bool => (p.1.2.zip p.2).filter f)
  funext a
  cases a.2 <;> rfl

private theorem droppedItems_primitive :
    Primrec (fun p : NormalForm.Code.RowData × List Bool => Code.droppedItems p.2 p.1.2) := by
  apply (selectedItems_primitive true).of_eq
  intro p
  unfold Code.droppedItems
  apply congrArg (fun xs : List (Item × Bool) => xs.map Prod.fst)
  apply congrArg (fun f : Item × Bool → Bool => (p.1.2.zip p.2).filter f)
  funext a
  cases a.2 <;> rfl

theorem remaining_primitive : Primrec₂ Code.remaining :=
  (Primrec.fst.comp Primrec.fst).pair keptItems_primitive

theorem dropped_primitive : Primrec₂ Code.dropped :=
  (Primrec.const (0 : Int)).pair droppedItems_primitive

theorem onlyPhi_primitive : Primrec Code.onlyPhi := by
  have hp : Primrec₂ (fun (_ : Unit) (a : Item) => a.2.1 == 1) :=
    Primrec.beq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) (Primrec.const 1)
  exact (LinearRowsCodeProof.listAll_primitive hp).comp (Primrec.const ()) Primrec.snd

theorem admissible_primitive :
    Primrec (fun p : Nat × NormalForm.Code.RowData × List Bool => Code.admissible p.1 p.2.1 p.2.2) := by
  let A := Nat × NormalForm.Code.RowData × List Bool
  have hr : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hlen : Primrec (fun p : A => p.2.2.length == p.2.1.2.length) :=
    Primrec.beq.comp (Primrec.list_length.comp hm)
      (Primrec.list_length.comp (Primrec.snd.comp hr))
  have hd := onlyPhi_primitive.comp (dropped_primitive.comp hr hm)
  have hl := LinearRowsCodeProof.rowLinear_primitive.comp Primrec.fst (remaining_primitive.comp hr hm)
  exact Primrec.and.comp (Primrec.and.comp hlen hd) hl

theorem masks_primitive : Primrec₂ Code.masks := by
  let A := Nat × NormalForm.Code.RowData
  have hlist : Primrec (fun p : A => CommonHeadLargeGuards.masks p.2.2.length) :=
    CommonHeadCode.Program.masks_primitive.comp (Primrec.list_length.comp (Primrec.snd.comp Primrec.snd))
  have hp : Primrec (fun p : A × List Bool => Code.admissible p.1.1 p.1.2 p.2) :=
    admissible_primitive.comp ((Primrec.fst.comp Primrec.fst).pair
      ((Primrec.snd.comp Primrec.fst).pair Primrec.snd))
  exact (filterWith_primitive hp.to₂).comp Primrec.id hlist

theorem actualMaskPrograms : InactivePhiProgramsTargets.ActualMaskPrograms :=
  ⟨remaining_primitive, dropped_primitive, onlyPhi_primitive, admissible_primitive, masks_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.InactivePhiProgramsProof
