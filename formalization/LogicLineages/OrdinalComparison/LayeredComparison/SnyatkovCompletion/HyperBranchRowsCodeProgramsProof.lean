module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SignedRowsCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperWindowProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsCodeProof
open HyperBranchRows
attribute [local irreducible] Nat.sqrt Nat.unpair

private theorem conjunction_primitive : Primrec₂ FiniteBranchRows.Code.conjunction :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair)
    (Primrec.const 4)

private theorem nonnegative_primitive : Primrec FiniteBranchRows.Code.nonnegative := by
  have ha : Primrec (fun row : NormalForm.Code.RowData =>
      ((0, 0, row) : NormalForm.Code.AtomData)) :=
    (Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id)
  exact Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) (Primrec.encode.comp ha)) (Primrec.const 2)

private theorem subtract_primitive : Primrec₂ (fun a b : Int => a - b) := by
  have h : Primrec (fun p : Int × Int => p.1 + -p.2) :=
    IntegerAlgorithms.Proof.add_primitive.comp Primrec.fst
      (IntegerAlgorithms.Proof.negate_primitive.comp Primrec.snd)
  simpa only [sub_eq_add_neg] using h.to₂

private theorem var_program {α : Type*} [Primcodable α] {i : α → Nat} (hi : Primrec i) :
    Primrec (fun x => FiniteBranchRows.Code.var (i x)) :=
  (Primrec.const 0).pair (hi.pair ((Primrec.const (0 : Int)).pair (Primrec.const (0 : Int))))

private theorem hyper_program {α : Type*} [Primcodable α]
    {i : α → Nat} {e h : α → Int}
    (hi : Primrec i) (he : Primrec e) (hh : Primrec h) :
    Primrec (fun x => FiniteBranchRows.Code.hyper (i x) (e x) (h x)) :=
  (Primrec.const 2).pair (hi.pair (he.pair hh))

private theorem leRow_program {α : Type*} [Primcodable α]
    {s t : α → NormalForm.Code.ItemData} {c : α → Nat}
    (hs : Primrec s) (ht : Primrec t) (hc : Primrec c) :
    Primrec (fun x => FiniteBranchRows.Code.leRow (s x) (t x) (c x)) :=
  (Primrec.const (0 : Int)).pair
    (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair hs)
      (Primrec.list_cons.comp ((IntegerAlgorithms.Proof.ofNat_primitive.comp hc).pair ht)
        (Primrec.const [])))

private theorem guardedLe_program {α : Type*} [Primcodable α]
    {s t : α → NormalForm.Code.ItemData} {c : α → Nat}
    (hs : Primrec s) (ht : Primrec t) (hc : Primrec c) :
    Primrec (fun x => FiniteBranchRows.Code.guardedLe (s x) (t x) (c x)) := by
  have hr := leRow_program hs ht hc
  exact conjunction_primitive.comp
    (FiniteBranchRowsCodeProof.domains_primitive.comp hr) (nonnegative_primitive.comp hr)

attribute [local irreducible] FiniteBranchRows.Code.guardedLe

private theorem leftName_primitive : Primrec HyperWindowCode.leftName :=
  Primrec.fst.comp Primrec.fst
private theorem rightName_primitive : Primrec HyperWindowCode.rightName :=
  Primrec.snd.comp Primrec.fst
private theorem leftIndex_primitive : Primrec HyperWindowCode.leftIndex :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
private theorem leftOuter_primitive : Primrec HyperWindowCode.leftOuter :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
private theorem rightIndex_primitive : Primrec HyperWindowCode.rightIndex :=
  Primrec.fst.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem rightOuter_primitive : Primrec HyperWindowCode.rightOuter :=
  Primrec.snd.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd))
private theorem coefficient_primitive : Primrec HyperWindowCode.coefficient :=
  Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
private theorem matrix_primitive : Primrec HyperWindowCode.matrix :=
  Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
private theorem leftBound_primitive : Primrec HyperWindowCode.leftBound :=
  HyperWindowProof.actualBoundPrograms.1.comp
    (leftIndex_primitive.pair (leftOuter_primitive.pair rightOuter_primitive))
private theorem rightBound_primitive : Primrec HyperWindowCode.rightBound :=
  HyperWindowProof.actualBoundPrograms.2.comp
    (leftOuter_primitive.pair (rightIndex_primitive.pair
      (rightOuter_primitive.pair coefficient_primitive)))

theorem closeGuard_primitive : Primrec Code.closeGuard := by
  have hs : Primrec (fun p : Code.Input => FiniteBranchRows.Code.hyper
      (HyperWindowCode.leftName p) (HyperWindowCode.leftIndex p) (HyperWindowCode.leftOuter p)) :=
    hyper_program leftName_primitive leftIndex_primitive leftOuter_primitive
  have ht : Primrec (fun p : Code.Input => FiniteBranchRows.Code.hyper
      (HyperWindowCode.rightName p) (HyperWindowCode.rightIndex p) (HyperWindowCode.rightOuter p)) :=
    hyper_program rightName_primitive rightIndex_primitive rightOuter_primitive
  exact conjunction_primitive.comp
    (guardedLe_program ht hs (Primrec.const 1))
    (guardedLe_program hs ht coefficient_primitive)

private theorem indexRow_program (a b : Int) {α : Type*} [Primcodable α]
    {i j : α → Nat} {z : α → Int} (hi : Primrec i) (hj : Primrec j) (hz : Primrec z) :
    Primrec (fun x => ((z x, [(a, FiniteBranchRows.Code.var (i x)),
      (b, FiniteBranchRows.Code.var (j x))]) : NormalForm.Code.RowData)) :=
  hz.pair (Primrec.list_cons.comp ((Primrec.const a).pair (var_program hi))
    (Primrec.list_cons.comp ((Primrec.const b).pair (var_program hj)) (Primrec.const [])))

theorem indexEquality_primitive : Primrec Code.indexEquality :=
  conjunction_primitive.comp
    (nonnegative_primitive.comp (indexRow_program 1 (-1) leftName_primitive rightName_primitive
      (subtract_primitive.comp leftIndex_primitive rightIndex_primitive)))
    (nonnegative_primitive.comp (indexRow_program (-1) 1 leftName_primitive rightName_primitive
      (subtract_primitive.comp rightIndex_primitive leftIndex_primitive)))

attribute [local irreducible] Code.closeGuard Code.indexEquality BoundedRows.Code.bounded
  SignedRows.Code.substitute

theorem leftCases_primitive : Primrec Code.leftCases :=
  BoundedRowsCodeProof.bounded_primitive.comp (leftName_primitive.pair leftBound_primitive)
    (conjunction_primitive.comp closeGuard_primitive matrix_primitive)

theorem rightCases_primitive : Primrec Code.rightCases :=
  BoundedRowsCodeProof.bounded_primitive.comp (rightName_primitive.pair rightBound_primitive)
    (conjunction_primitive.comp closeGuard_primitive matrix_primitive)

theorem equalCases_primitive : Primrec Code.equalCases :=
  SignedRowsCodeProof.substitute_primitive.comp
    ((leftName_primitive.pair rightName_primitive).pair
      (subtract_primitive.comp rightIndex_primitive leftIndex_primitive))
    (conjunction_primitive.comp indexEquality_primitive
      (conjunction_primitive.comp closeGuard_primitive matrix_primitive))

theorem actualBranchNumericPrograms : HyperBranchRowsTargets.ActualBranchNumericPrograms :=
  ⟨leftCases_primitive, rightCases_primitive, equalCases_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.HyperBranchRowsCodeProof
