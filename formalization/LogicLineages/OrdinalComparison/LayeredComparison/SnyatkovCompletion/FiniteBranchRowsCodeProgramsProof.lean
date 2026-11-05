module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BoundedRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsCodeProof
open FiniteBranchRows
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem conjunction_primitive : Primrec₂ Code.conjunction :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair)
    (Primrec.const 4)

private theorem nonnegative_primitive : Primrec Code.nonnegative := by
  have ha : Primrec (fun row : NormalForm.Code.RowData =>
      ((0, 0, row) : NormalForm.Code.AtomData)) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id)
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.encode.comp ha)) (Primrec.const 2)

private theorem nonlinear_program {α : Type*} [Primcodable α]
    {i : α → Nat} {kind : α → Bool} {e h : α → Int}
    (hi : Primrec i) (hk : Primrec kind) (he : Primrec e) (hh : Primrec h) :
    Primrec (fun x => Code.nonlinear (i x) (kind x) (e x) (h x)) :=
  Primrec.ite (Primrec.eq.comp hk (Primrec.const true))
    ((Primrec.const 2).pair (hi.pair (he.pair hh)))
    ((Primrec.const 1).pair (hi.pair (he.pair (Primrec.const (0 : Int)))))

private theorem var_program {α : Type*} [Primcodable α] {i : α → Nat} (hi : Primrec i) :
    Primrec (fun x => Code.var (i x)) :=
  (Primrec.const 0).pair (hi.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))

private theorem phi_program {α : Type*} [Primcodable α]
    {i : α → Nat} {e : α → Int} (hi : Primrec i) (he : Primrec e) :
    Primrec (fun x => Code.phi (i x) (e x)) :=
  (Primrec.const 1).pair (hi.pair (he.pair (Primrec.const (0 : Int))))

private theorem hyper_program {α : Type*} [Primcodable α]
    {i : α → Nat} {e h : α → Int}
    (hi : Primrec i) (he : Primrec e) (hh : Primrec h) :
    Primrec (fun x => Code.hyper (i x) (e x) (h x)) :=
  (Primrec.const 2).pair (hi.pair (he.pair hh))

private theorem leRow_program {α : Type*} [Primcodable α]
    {s t : α → NormalForm.Code.ItemData} {c : α → Nat}
    (hs : Primrec s) (ht : Primrec t) (hc : Primrec c) :
    Primrec (fun x => Code.leRow (s x) (t x) (c x)) :=
  (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair hs)
      (Primrec.list_cons.comp ((IntegerAlgorithms.Proof.ofNat_primitive.comp hc).pair ht)
        (Primrec.const [])))

private theorem domainRowData_primitive : Primrec NormalForm.Code.domainRowData := by
  have hn : Primrec (fun s : NormalForm.Code.ItemData => s.2.1) :=
    Primrec.fst.comp Primrec.snd
  have hv : Primrec (fun s : NormalForm.Code.ItemData =>
      ((0 : Nat), s.2.1, (0 : Int), (0 : Int))) :=
    (Primrec.const 0).pair (hn.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))
  have hl : Primrec (fun s : NormalForm.Code.ItemData =>
      [((1 : Int), ((0 : Nat), s.2.1, (0 : Int), (0 : Int)))]) :=
    Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair hv) (Primrec.const [])
  exact (IntegerAlgorithms.Proof.negate_primitive.comp
    (IntegerAlgorithms.Proof.ofNat_primitive.comp NormalFormCodeProof.itemCutoff_primitive)).pair hl

theorem domains_primitive : Primrec Code.domains := by
  have hs : Primrec (fun p : NormalForm.Code.RowData × ((Int × NormalForm.Code.ItemData) × Nat) =>
      Code.conjunction (Code.nonnegative (NormalForm.Code.domainRowData p.2.1.2)) p.2.2) :=
    conjunction_primitive.comp
      (nonnegative_primitive.comp (domainRowData_primitive.comp
        (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))))
      (Primrec.snd.comp Primrec.snd)
  exact Primrec.list_foldr Primrec.snd (Primrec.const 0) hs.to₂

attribute [local irreducible] Code.domains

private theorem guardedLe_program {α : Type*} [Primcodable α]
    {s t : α → NormalForm.Code.ItemData} {c : α → Nat}
    (hs : Primrec s) (ht : Primrec t) (hc : Primrec c) :
    Primrec (fun x => Code.guardedLe (s x) (t x) (c x)) := by
  have hr := leRow_program hs ht hc
  exact conjunction_primitive.comp (domains_primitive.comp hr) (nonnegative_primitive.comp hr)

attribute [local irreducible] Code.guardedLe

namespace LinearInput
private theorem leftName : Primrec LinearWindow.Code.leftName := Primrec.fst.comp Primrec.fst
private theorem rightName : Primrec LinearWindow.Code.rightName := Primrec.snd.comp Primrec.fst
private theorem leftKind : Primrec LinearWindow.Code.leftKind :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
private theorem rightKind : Primrec LinearWindow.Code.rightKind :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
private theorem leftIndex : Primrec LinearWindow.Code.leftIndex :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem leftOuter : Primrec LinearWindow.Code.leftOuter :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem rightIndex : Primrec LinearWindow.Code.rightIndex :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
private theorem rightOuter : Primrec LinearWindow.Code.rightOuter :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
private theorem coefficient : Primrec LinearWindow.Code.coefficient :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
private theorem matrix : Primrec LinearWindow.Code.matrix :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))

private theorem budget : Primrec (fun p : LinearWindow.Code.Input =>
    LinearWindow.shiftBudget (LinearWindow.Code.rightKind p)
      (LinearWindow.Code.rightIndex p) (LinearWindow.Code.rightOuter p)) :=
  Primrec.nat_add.comp (IntegerAlgorithms.Proof.abs_primitive.comp rightIndex)
    (Primrec.ite (Primrec.eq.comp rightKind (Primrec.const true))
      (IntegerAlgorithms.Proof.abs_primitive.comp rightOuter) (Primrec.const 0))

private theorem bound : Primrec LinearWindow.Code.bound :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp coefficient (Primrec.nat_mul.comp coefficient budget)) budget)
    (Primrec.const 1)
end LinearInput

namespace ActiveInput
private theorem leftName : Primrec ActiveHyper.Code.leftName := Primrec.fst.comp Primrec.fst
private theorem rightName : Primrec ActiveHyper.Code.rightName := Primrec.snd.comp Primrec.fst
private theorem kind : Primrec ActiveHyper.Code.kind := Primrec.fst.comp Primrec.snd
private theorem leftIndex : Primrec ActiveHyper.Code.leftIndex :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem leftOuter : Primrec ActiveHyper.Code.leftOuter :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem activeIndex : Primrec ActiveHyper.Code.activeIndex :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
private theorem activeOuter : Primrec ActiveHyper.Code.activeOuter :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
private theorem plainShift : Primrec ActiveHyper.Code.plainShift :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
private theorem coefficient : Primrec ActiveHyper.Code.coefficient :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
private theorem matrix : Primrec ActiveHyper.Code.matrix :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))

private theorem bound : Primrec ActiveHyper.Code.bound :=
  Primrec.nat_add.comp
    (Primrec.nat_add.comp
      (Primrec.nat_add.comp
        (Primrec.nat_add.comp coefficient
          (Primrec.nat_mul.comp (Primrec.const 2)
            (IntegerAlgorithms.Proof.abs_primitive.comp activeIndex)))
        (IntegerAlgorithms.Proof.abs_primitive.comp activeOuter))
      (IntegerAlgorithms.Proof.abs_primitive.comp plainShift))
    (Primrec.const 1)
end ActiveInput

theorem linearGuard_primitive : Primrec Code.linearGuard := by
  have hlead : Primrec (fun p : LinearWindow.Code.Input =>
      Code.nonlinear (LinearWindow.Code.leftName p) (LinearWindow.Code.leftKind p)
        (LinearWindow.Code.leftIndex p) (LinearWindow.Code.leftOuter p)) :=
    nonlinear_program LinearInput.leftName LinearInput.leftKind
      LinearInput.leftIndex LinearInput.leftOuter
  have hactive : Primrec (fun p : LinearWindow.Code.Input =>
      Code.nonlinear (LinearWindow.Code.rightName p) (LinearWindow.Code.rightKind p)
        (LinearWindow.Code.rightIndex p) (LinearWindow.Code.rightOuter p)) :=
    nonlinear_program LinearInput.rightName LinearInput.rightKind
      LinearInput.rightIndex LinearInput.rightOuter
  exact conjunction_primitive.comp
    (guardedLe_program hactive hlead (Primrec.const 1))
    (guardedLe_program hlead (var_program LinearInput.rightName) LinearInput.coefficient)

theorem activeGuard_primitive : Primrec Code.activeGuard := by
  have hlead : Primrec (fun p : ActiveHyper.Code.Input =>
      Code.nonlinear (ActiveHyper.Code.leftName p) (ActiveHyper.Code.kind p)
        (ActiveHyper.Code.leftIndex p) (ActiveHyper.Code.leftOuter p)) :=
    nonlinear_program ActiveInput.leftName ActiveInput.kind
      ActiveInput.leftIndex ActiveInput.leftOuter
  have hactive : Primrec (fun p : ActiveHyper.Code.Input =>
      Code.hyper (ActiveHyper.Code.rightName p) (ActiveHyper.Code.activeIndex p)
        (ActiveHyper.Code.activeOuter p)) :=
    hyper_program ActiveInput.rightName ActiveInput.activeIndex ActiveInput.activeOuter
  have hplain : Primrec (fun p : ActiveHyper.Code.Input =>
      Code.phi (ActiveHyper.Code.rightName p) (ActiveHyper.Code.plainShift p)) :=
    phi_program ActiveInput.rightName ActiveInput.plainShift
  exact conjunction_primitive.comp
    (guardedLe_program hactive hlead (Primrec.const 1))
    (guardedLe_program hlead hplain ActiveInput.coefficient)

attribute [local irreducible] Code.linearGuard Code.activeGuard BoundedRows.Code.bounded

/-- The original finite bound is computed from the packed source data; the
radix-six guard and matrix then enter the actual normal-form bounded compiler. -/
theorem linearCases_primitive : Primrec Code.linearCases :=
  BoundedRowsCodeProof.bounded_primitive.comp (LinearInput.rightName.pair LinearInput.bound)
    (conjunction_primitive.comp linearGuard_primitive LinearInput.matrix)

theorem activeCases_primitive : Primrec Code.activeCases :=
  BoundedRowsCodeProof.bounded_primitive.comp (ActiveInput.rightName.pair ActiveInput.bound)
    (conjunction_primitive.comp activeGuard_primitive ActiveInput.matrix)

theorem actualBranchNumericPrograms : FiniteBranchRowsTargets.ActualBranchNumericPrograms :=
  ⟨linearCases_primitive, activeCases_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsCodeProof
