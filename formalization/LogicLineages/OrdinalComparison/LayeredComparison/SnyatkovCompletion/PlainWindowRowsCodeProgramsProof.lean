module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NestedRowsCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.FiniteBranchRowsCodeProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsCodeProof
open PlainWindowRows
attribute [local irreducible] Nat.sqrt Nat.unpair NestedRows.Code.substitute

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

private theorem phi_program {α : Type*} [Primcodable α]
    {i : α → Nat} {e : α → Int} (hi : Primrec i) (he : Primrec e) :
    Primrec (fun x => FiniteBranchRows.Code.phi (i x) (e x)) :=
  (Primrec.const 1).pair (hi.pair (he.pair (Primrec.const (0 : Int))))

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

private theorem leftName_primitive : Primrec Code.leftName := Primrec.fst.comp Primrec.fst
private theorem rightName_primitive : Primrec Code.rightName := Primrec.snd.comp Primrec.fst
private theorem leftShift_primitive : Primrec Code.leftShift :=
  Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
private theorem rightShift_primitive : Primrec Code.rightShift :=
  Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
private theorem coefficient_primitive : Primrec Code.coefficient :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
private theorem body_primitive : Primrec Code.body :=
  Primrec.snd.comp (Primrec.snd.comp Primrec.snd)

theorem plusGuard_primitive : Primrec Code.plusGuard := by
  have hs : Primrec (fun p : Code.Input =>
      FiniteBranchRows.Code.phi (Code.leftName p) (Code.leftShift p)) :=
    phi_program leftName_primitive leftShift_primitive
  have ht : Primrec (fun p : Code.Input =>
      FiniteBranchRows.Code.phi (Code.rightName p) (Code.rightShift p)) :=
    phi_program rightName_primitive rightShift_primitive
  exact conjunction_primitive.comp
    (guardedLe_program ht hs (Primrec.const 1)) (guardedLe_program hs ht coefficient_primitive)

theorem minusGuard_primitive : Primrec Code.minusGuard := by
  have hs : Primrec (fun p : Code.Input =>
      FiniteBranchRows.Code.phi (Code.leftName p) (Code.leftShift p)) :=
    phi_program leftName_primitive leftShift_primitive
  have ht : Primrec (fun p : Code.Input =>
      FiniteBranchRows.Code.phi (Code.rightName p) (Code.rightShift p)) :=
    phi_program rightName_primitive rightShift_primitive
  exact conjunction_primitive.comp
    (guardedLe_program hs ht (Primrec.const 1)) (guardedLe_program ht hs coefficient_primitive)

attribute [local irreducible] Code.plusGuard Code.minusGuard

theorem plusSubstitute_primitive : Primrec₂ Code.plusSubstitute :=
  NestedRowsCodeProof.substitute_primitive.comp
    (((leftName_primitive.comp Primrec.fst).pair (rightName_primitive.comp Primrec.fst)).pair
      ((rightShift_primitive.comp Primrec.fst).pair
        (subtract_primitive.comp (IntegerAlgorithms.Proof.ofNat_primitive.comp Primrec.snd)
          (leftShift_primitive.comp Primrec.fst))))
    (body_primitive.comp Primrec.fst)

theorem minusSubstitute_primitive : Primrec₂ Code.minusSubstitute :=
  NestedRowsCodeProof.substitute_primitive.comp
    (((leftName_primitive.comp Primrec.fst).pair (rightName_primitive.comp Primrec.fst)).pair
      ((subtract_primitive.comp (rightShift_primitive.comp Primrec.fst)
          (IntegerAlgorithms.Proof.ofNat_primitive.comp Primrec.snd)).pair
        (IntegerAlgorithms.Proof.negate_primitive.comp (leftShift_primitive.comp Primrec.fst))))
    (body_primitive.comp Primrec.fst)

attribute [local irreducible] Code.plusSubstitute Code.minusSubstitute

private def withGuard (guard : Code.Input → Nat) (p : Code.Input) : Code.Input :=
  Code.input (Code.leftName p) (Code.rightName p) (Code.leftShift p) (Code.rightShift p)
    (Code.coefficient p) (FiniteBranchRows.Code.conjunction (guard p) (Code.body p))

private theorem withGuard_primitive {guard : Code.Input → Nat} (hg : Primrec guard) :
    Primrec (withGuard guard) :=
  (leftName_primitive.pair rightName_primitive).pair
    ((leftShift_primitive.pair rightShift_primitive).pair
      (coefficient_primitive.pair (conjunction_primitive.comp hg body_primitive)))

theorem plusCases_primitive : Primrec Code.plusCases := by
  have hi : Primrec (withGuard Code.plusGuard) := withGuard_primitive plusGuard_primitive
  have hs : Primrec₂ (fun p : Code.Input => Code.plusSubstitute (withGuard Code.plusGuard p)) :=
    plusSubstitute_primitive.comp (hi.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : Code.Input => (List.range (Code.coefficient p + 1)).map
      (fun d => Code.plusSubstitute (withGuard Code.plusGuard p) d)) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_add.comp coefficient_primitive (Primrec.const 1))) hs
  exact BoundedRowsCodeProof.any_primitive.comp hm

theorem minusCases_primitive : Primrec Code.minusCases := by
  have hi : Primrec (withGuard Code.minusGuard) := withGuard_primitive minusGuard_primitive
  have hs : Primrec₂ (fun p : Code.Input => Code.minusSubstitute (withGuard Code.minusGuard p)) :=
    minusSubstitute_primitive.comp (hi.comp Primrec.fst) Primrec.snd
  have hm : Primrec (fun p : Code.Input => (List.range (Code.coefficient p + 1)).map
      (fun d => Code.minusSubstitute (withGuard Code.minusGuard p) d)) :=
    Primrec.list_map
      (Primrec.list_range.comp (Primrec.nat_add.comp coefficient_primitive (Primrec.const 1))) hs
  exact BoundedRowsCodeProof.any_primitive.comp hm

theorem actualBranchNumericPrograms : PlainWindowRowsTargets.ActualBranchNumericPrograms :=
  ⟨plusCases_primitive, minusCases_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.PlainWindowRowsCodeProof
