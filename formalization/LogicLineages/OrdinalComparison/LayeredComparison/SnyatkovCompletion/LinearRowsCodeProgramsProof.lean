module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProof
open LinearRows
attribute [local irreducible] Nat.sqrt Nat.unpair
attribute [local irreducible] Code.rowConst Code.rowAdd Code.rowScale
  Code.leading Code.remainder Code.rowLinear Code.decodeAtom Code.decodeUnit
  Code.weight Code.nonzeroSign Code.conjunction Code.unitAtom

theorem coefficientModulus_primitive : Primrec₂ Code.coefficientModulus := by
  let A := Nat × Nat
  have hw : Primrec (fun p : A × Nat => Code.weight p.1.1 (Code.decodeAtom p.2)) :=
    weight_primitive.comp (Primrec.fst.comp Primrec.fst)
      (decodeAtom_primitive.comp Primrec.snd)
  have hm : Primrec (fun p : A =>
      (Code.atoms p.2).map (fun a => Code.weight p.1 (Code.decodeAtom a))) :=
    Primrec.list_map (atoms_primitive.comp Primrec.snd) hw.to₂
  exact naturalProduct_primitive.comp hm

attribute [local irreducible] Code.coefficientModulus

theorem adjustAtom_primitive :
    Primrec₂ (fun args : Nat × Nat => Code.adjustAtom args.1 args.2) := by
  let A := (Nat × Nat) × Code.AtomData
  have hi : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have hM : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have ht : Primrec (fun p : A => p.2.1) := Primrec.fst.comp Primrec.snd
  have hm : Primrec (fun p : A => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hrow : Primrec (fun p : A => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hz : Primrec (fun p : A => Code.leading p.1.1 p.2.2.2) :=
    leading_primitive.comp hi hrow
  have hr : Primrec (fun p : A => Code.remainder p.1.1 p.2.2.2) :=
    remainder_primitive.comp hi hrow
  have hk : Primrec (fun p : A => p.1.2 / (Code.leading p.1.1 p.2.2.2).natAbs) :=
    Primrec.nat_div.comp hM (IntegerAlgorithms.Proof.abs_primitive.comp hz)
  have hmod : Primrec (fun p : A =>
      (p.2.2.1 + 1) * (p.1.2 / (Code.leading p.1.1 p.2.2.2).natAbs) - 1) :=
    Primrec.nat_sub.comp
      (Primrec.nat_mul.comp (Primrec.nat_add.comp hm (Primrec.const 1)) hk) (Primrec.const 1)
  have hzero : Primrec (fun p : A =>
      ((p.2.1, p.2.2.1, (0 : Int), Code.remainder p.1.1 p.2.2.2) : Code.UnitAtomData)) :=
    ht.pair (hm.pair ((Primrec.const (0 : Int)).pair hr))
  have hnonzero : Primrec (fun p : A =>
      ((p.2.1,
        if p.2.1 = 0 then 0
        else (p.2.2.1 + 1) * (p.1.2 / (Code.leading p.1.1 p.2.2.2).natAbs) - 1,
        Code.nonzeroSign (Code.leading p.1.1 p.2.2.2),
        Code.rowScale ((p.1.2 / (Code.leading p.1.1 p.2.2.2).natAbs : Nat) : Int)
          (Code.remainder p.1.1 p.2.2.2)) : Code.UnitAtomData)) :=
    ht.pair ((Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) (Primrec.const 0) hmod).pair
      ((nonzeroSign_primitive.comp hz).pair
        (rowScale_primitive.comp (IntegerAlgorithms.Proof.ofNat_primitive.comp hk) hr)))
  exact Primrec.ite (Primrec.eq.comp hz (Primrec.const (0 : Int))) hzero hnonzero

attribute [local irreducible] Code.adjustAtom

theorem adjust_primitive :
    Primrec₂ (fun args : Nat × Nat => Code.adjust args.1 args.2) := by
  have hp : Primrec₂ (fun args : Nat × Nat => fun a : Nat =>
      Encodable.encode (Code.adjustAtom args.1 args.2 (Code.decodeAtom a))) :=
    Primrec.encode.comp (adjustAtom_primitive.comp Primrec.fst
      (decodeAtom_primitive.comp Primrec.snd))
  exact mapAtoms_primitive hp

attribute [local irreducible] Code.adjust

theorem normalize_primitive : Primrec₂ Code.normalize := by
  let A := Nat × Nat
  have hguard : Primrec (fun p : A =>
      ((1, Code.coefficientModulus p.1 p.2 - 1, (1 : Int), Code.rowConst 0) : Code.UnitAtomData)) :=
    (Primrec.const 1).pair
      ((Primrec.nat_sub.comp coefficientModulus_primitive (Primrec.const 1)).pair
        ((Primrec.const (1 : Int)).pair (Primrec.const (Code.rowConst 0))))
  exact conjunction_primitive.comp (unitAtom_primitive.comp hguard)
    (adjust_primitive.comp (Primrec.fst.pair coefficientModulus_primitive) Primrec.snd)

attribute [local irreducible] Code.normalize

theorem atomPeriod_primitive : Primrec Code.atomPeriod :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.const 1)
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))

theorem atomCutoffs_primitive : Primrec Code.atomCutoffs := by
  have hs : Primrec (fun a : Code.UnitAtomData => a.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hr : Primrec (fun a : Code.UnitAtomData => a.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hp : Primrec (fun a : Code.UnitAtomData => [Code.rowScale (-1) a.2.2.2]) :=
    Primrec.list_cons.comp (rowScale_primitive.comp (Primrec.const (-1 : Int)) hr)
      (Primrec.const [])
  have hn : Primrec (fun a : Code.UnitAtomData => [Code.rowAdd a.2.2.2 (Code.rowConst 1)]) :=
    Primrec.list_cons.comp (rowAdd_primitive.comp hr (Primrec.const (Code.rowConst 1)))
      (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    (Primrec.ite (Primrec.eq.comp hs (Primrec.const (1 : Int))) hp
      (Primrec.ite (Primrec.eq.comp hs (Primrec.const (-1 : Int))) hn (Primrec.const [])))
    (Primrec.const [])

attribute [local irreducible] Code.atomPeriod Code.atomCutoffs

theorem period_primitive : Primrec Code.period := by
  have hp : Primrec₂ (fun (_ : Nat) a => Code.atomPeriod (Code.decodeUnit a)) :=
    atomPeriod_primitive.comp (decodeUnit_primitive.comp Primrec.snd)
  exact naturalProduct_primitive.comp (Primrec.list_map atoms_primitive hp)

theorem cutoffs_primitive : Primrec Code.cutoffs := by
  have hp : Primrec₂ (fun (_ : Nat) a => Code.atomCutoffs (Code.decodeUnit a)) :=
    atomCutoffs_primitive.comp (decodeUnit_primitive.comp Primrec.snd)
  exact Primrec.list_cons.comp (Primrec.const (Code.rowConst 0))
    (Primrec.list_flatMap atoms_primitive hp)

attribute [local irreducible] Code.period Code.cutoffs

theorem instantiateAtom_primitive : Primrec₂ Code.instantiateAtom := by
  let A := Code.RowData × Code.UnitAtomData
  have hs : Primrec (fun p : A => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hr : Primrec (fun p : A => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  exact (Primrec.fst.comp Primrec.snd).pair
    ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (rowAdd_primitive.comp (rowScale_primitive.comp hs Primrec.fst) hr))

attribute [local irreducible] Code.instantiateAtom

theorem instantiate_primitive : Primrec₂ Code.instantiate := by
  have hp : Primrec₂ (fun b : Code.RowData => fun a : Nat =>
      Encodable.encode (Code.instantiateAtom b (Code.decodeUnit a))) :=
    Primrec.encode.comp (instantiateAtom_primitive.comp Primrec.fst
      (decodeUnit_primitive.comp Primrec.snd))
  exact (mapAtoms_primitive hp).comp Primrec.snd Primrec.fst

attribute [local irreducible] Code.instantiate

theorem guarded_primitive : Primrec Code.guarded :=
  conjunction_primitive.comp
    (Primrec.const (Code.unitAtom (0, 0, 1, Code.rowConst 0))) Primrec.id

attribute [local irreducible] Code.guarded

theorem unitEliminate_primitive : Primrec Code.unitEliminate := by
  let A := Nat × Code.RowData
  have hj : Primrec (fun p : A × Int =>
      Code.instantiate (Code.guarded p.1.1) (Code.rowAdd p.1.2 (Code.rowConst p.2))) :=
    instantiate_primitive.comp (guarded_primitive.comp (Primrec.fst.comp Primrec.fst))
      (rowAdd_primitive.comp (Primrec.snd.comp Primrec.fst)
        (rowConst_primitive.comp Primrec.snd))
  have hnat : Primrec (fun p : A => List.range (Code.period p.1)) :=
    Primrec.list_range.comp (period_primitive.comp Primrec.fst)
  have hint : Primrec (fun p : A =>
      (List.range (Code.period p.1)).map (fun j : Nat => (j : Int))) :=
    Primrec.list_map hnat (IntegerAlgorithms.Proof.ofNat_primitive.comp Primrec.snd).to₂
  have hm : Primrec (fun p : A =>
      ((List.range (Code.period p.1)).map (fun j : Nat => (j : Int))).map
        (fun j => Code.instantiate (Code.guarded p.1) (Code.rowAdd p.2 (Code.rowConst j)))) :=
    Primrec.list_map hint hj.to₂
  have he : Primrec (fun code : Nat => (Code.cutoffs code).flatMap (fun b =>
      ((List.range (Code.period code)).map (fun j : Nat => (j : Int))).map
        (fun j => Code.instantiate (Code.guarded code) (Code.rowAdd b (Code.rowConst j))))) :=
    Primrec.list_flatMap cutoffs_primitive hm.to₂
  apply (BoundedRowsCodeProof.any_primitive.comp he).of_eq
  intro code
  simp only [Code.unitEliminate, List.bind_eq_flatMap, List.flatMap_cons, List.flatMap_nil,
    List.map_eq_flatMap]
  rfl

attribute [local irreducible] Code.unitEliminate

theorem eliminate_primitive : Primrec₂ Code.eliminate :=
  unitEliminate_primitive.comp normalize_primitive

theorem actualNumericPrograms : LinearRowsTargets.ActualNumericPrograms :=
  ⟨isLinear_primitive, normalize_primitive, unitEliminate_primitive, eliminate_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeProof
