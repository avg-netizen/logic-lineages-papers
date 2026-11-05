module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeRecursionProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProof
open LinearRows
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem listAll_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    {p : α → β → Bool} (hp : Primrec₂ p) :
    Primrec₂ (fun (a : α) (xs : List β) => xs.all (p a)) := by
  let A := α × List β
  have hs : Primrec (fun q : A × (β × Bool) => p q.1.1 q.2.1 && q.2.2) :=
    Primrec.and.comp
      (hp.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun q : A => q.2.foldr (fun b s => p q.1 b && s) true) :=
    Primrec.list_foldr Primrec.snd (Primrec.const true) hs.to₂
  apply hf.to₂.of_eq
  intro a xs
  induction xs with
  | nil => rfl
  | cons b xs ih => simp only [List.foldr_cons, List.all_cons, ih]

private theorem listFilter_primitive {α β : Type*} [Primcodable α] [Primcodable β]
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

private theorem integerSum_primitive : Primrec (fun xs : List Int => xs.sum) := by
  have hs : Primrec (fun p : List Int × (Int × Int) => p.2.1 + p.2.2) :=
    IntegerAlgorithms.Proof.add_primitive.comp
      (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Int => xs.foldr (fun a b => a + b) 0) :=
    Primrec.list_foldr Primrec.id (Primrec.const (0 : Int)) hs.to₂
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, List.sum_cons, ih]

theorem naturalProduct_primitive : Primrec (fun xs : List Nat => xs.prod) := by
  have hs : Primrec (fun p : List Nat × (Nat × Nat) => p.2.1 * p.2.2) :=
    Primrec.nat_mul.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)
  have hf : Primrec (fun xs : List Nat => xs.foldr (fun a b => a * b) 1) :=
    Primrec.list_foldr Primrec.id (Primrec.const (1 : Nat)) hs.to₂
  apply hf.of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons a xs ih => simp only [List.foldr_cons, List.prod_cons, ih]

theorem rowConst_primitive : Primrec Code.rowConst :=
  Primrec.id.pair (Primrec.const [])

theorem rowAdd_primitive : Primrec₂ Code.rowAdd :=
  (IntegerAlgorithms.Proof.add_primitive.comp
    (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
  (Primrec.list_append.comp
    (Primrec.snd.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))

theorem rowScale_primitive : Primrec₂ Code.rowScale := by
  let I := Int × NormalForm.Code.ItemData
  let A := Int × Code.RowData
  have hs : Primrec (fun p : A × I => (p.1.1 * p.2.1, p.2.2)) :=
    (IntegerAlgorithms.Proof.mul_primitive.comp
      (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)).pair
      (Primrec.snd.comp Primrec.snd)
  have hm : Primrec (fun p : A => p.2.2.map (fun a => (p.1 * a.1, a.2))) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) hs.to₂
  exact (IntegerAlgorithms.Proof.mul_primitive.comp Primrec.fst
    (Primrec.fst.comp Primrec.snd)).pair hm

attribute [local irreducible] Code.rowConst Code.rowAdd Code.rowScale

private theorem itemName_primitive :
    Primrec (fun a : Int × NormalForm.Code.ItemData => a.2.2.1) :=
  Primrec.fst.comp (Primrec.snd.comp Primrec.snd)

theorem leading_primitive : Primrec₂ Code.leading := by
  let I := Int × NormalForm.Code.ItemData
  let A := Nat × Code.RowData
  have hs : Primrec (fun p : A × I => if p.2.2.2.1 = p.1.1 then p.2.1 else (0 : Int)) :=
    Primrec.ite
      (Primrec.eq.comp (itemName_primitive.comp Primrec.snd) (Primrec.fst.comp Primrec.fst))
      (Primrec.fst.comp Primrec.snd) (Primrec.const (0 : Int))
  have hm : Primrec (fun p : A =>
      p.2.2.map (fun a => if a.2.2.1 = p.1 then a.1 else (0 : Int))) :=
    Primrec.list_map (Primrec.snd.comp Primrec.snd) hs.to₂
  exact integerSum_primitive.comp hm

theorem remainder_primitive : Primrec₂ Code.remainder := by
  let I := Int × NormalForm.Code.ItemData
  have hp : Primrec₂ (fun i : Nat => fun a : I => a.2.2.1 != i) :=
    Primrec.not.comp (Primrec.beq.comp (itemName_primitive.comp Primrec.snd) Primrec.fst)
  exact (Primrec.fst.comp Primrec.snd).pair
    ((listFilter_primitive hp).comp Primrec.fst (Primrec.snd.comp Primrec.snd))

theorem rowLinear_primitive : Primrec₂ Code.rowLinear := by
  let I := Int × NormalForm.Code.ItemData
  have ht : Primrec (fun p : Nat × I => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hn : Primrec (fun p : Nat × I => p.2.2.2.1) := itemName_primitive.comp Primrec.snd
  have hp : Primrec₂ (fun i : Nat => fun a : I => a.2.1 == 0 || a.2.2.1 != i) :=
    Primrec.or.comp (Primrec.beq.comp ht (Primrec.const 0))
      (Primrec.not.comp (Primrec.beq.comp hn Primrec.fst))
  exact (listAll_primitive hp).comp Primrec.fst (Primrec.snd.comp Primrec.snd)

attribute [local irreducible] Code.leading Code.remainder Code.rowLinear

theorem decodeAtom_primitive : Primrec Code.decodeAtom :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option Code.AtomData)))
    (Primrec.const (0, 0, (0 : Int), []))

theorem decodeUnit_primitive : Primrec Code.decodeUnit :=
  Primrec.option_getD.comp
    (Primrec.decode : Primrec (fun n : Nat => (Encodable.decode n : Option Code.UnitAtomData)))
    (Primrec.const (0, 0, (0 : Int), (0 : Int), []))

attribute [local irreducible] Code.decodeAtom Code.decodeUnit

theorem isLinear_primitive : Primrec₂ Code.isLinear := by
  have hp : Primrec₂ (fun i a : Nat => Code.rowLinear i (Code.decodeAtom a).2.2) :=
    rowLinear_primitive.comp Primrec.fst
      (Primrec.snd.comp (Primrec.snd.comp (decodeAtom_primitive.comp Primrec.snd)))
  exact (listAll_primitive hp).comp Primrec.fst (atoms_primitive.comp Primrec.snd)

theorem conjunction_primitive : Primrec₂ Code.conjunction :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) Primrec₂.natPair) (Primrec.const 4)

theorem unitAtom_primitive : Primrec Code.unitAtom :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 6) Primrec.encode) (Primrec.const 2)

theorem weight_primitive : Primrec₂ Code.weight := by
  have hz : Primrec (fun p : Nat × Code.AtomData => Code.leading p.1 p.2.2.2) :=
    leading_primitive.comp Primrec.fst
      (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact Primrec.ite (Primrec.eq.comp hz (Primrec.const (0 : Int)))
    (Primrec.const 1) (IntegerAlgorithms.Proof.abs_primitive.comp hz)

theorem nonzeroSign_primitive : Primrec Code.nonzeroSign := by
  have hp : PrimrecPred (fun z : Int => 0 < z) :=
    (Primrec.eq.comp IntegerAlgorithms.Proof.sign_primitive (Primrec.const (1 : Int))).of_eq
      (fun z => Int.sign_eq_one_iff_pos)
  exact Primrec.ite hp (Primrec.const (1 : Int)) (Primrec.const (-1 : Int))

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProof
