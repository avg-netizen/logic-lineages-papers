module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeLiftProgramsProof
public import LogicLineages.OrdinalComparison.ControlResidueProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
open PlainBlockLinearizationCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair


theorem binary_primitive (base tag : Nat) : Primrec₂ (fun a b : Nat => base * Nat.pair a b + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec₂.natPair) (Primrec.const tag)
#print axioms binary_primitive

theorem unary_primitive (base tag : Nat) : Primrec (fun a : Nat => base * a + tag) :=
  Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const base) Primrec.id) (Primrec.const tag)
#print axioms unary_primitive

theorem subtract_primitive : Primrec₂ WindowCode.subtract := binary_primitive 10 3
#print axioms subtract_primitive

theorem numeral_primitive : Primrec WindowCode.numeral :=
  Primrec.nat_mul.comp (Primrec.const 10) Primrec.id
#print axioms numeral_primitive

theorem nonnegative_primitive : Primrec nonnegative :=
  (unary_primitive 6 2).comp (Primrec.encode.comp ((Primrec.const 0).pair ((Primrec.const 0).pair Primrec.id)))
#print axioms nonnegative_primitive

theorem divisible_primitive : Primrec₂ divisible :=
  (unary_primitive 6 2).comp (Primrec.encode.comp ((Primrec.const 1).pair (Primrec.fst.pair Primrec.snd)))
#print axioms divisible_primitive

theorem conjunction_primitive : Primrec₂ conjunction := binary_primitive 6 4
#print axioms conjunction_primitive

theorem disjunction_primitive : Primrec₂ disjunction := binary_primitive 6 5
#print axioms disjunction_primitive

theorem all_primitive : Primrec all :=
  Primrec.list_foldr Primrec.id (Primrec.const 0)
    (conjunction_primitive.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂
#print axioms all_primitive

theorem sum_int_primitive : Primrec (fun xs : List Int => xs.sum) := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const (0 : Int))
    (IntegerAlgorithms.Proof.add_primitive.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [id_eq, List.foldr_cons, List.sum_cons] at ih ⊢
      rw [ih]
#print axioms sum_int_primitive

theorem sum_nat_primitive : Primrec (fun xs : List Nat => xs.sum) := by
  apply (Primrec.list_foldr Primrec.id (Primrec.const (0 : Nat))
    (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro xs
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      simp only [id_eq, List.foldr_cons, List.sum_cons] at ih ⊢
      rw [ih]
#print axioms sum_nat_primitive

theorem filter_primitive {α β : Type*} [Primcodable α] [Primcodable β]
    {pred : α → β → Bool} (hp : Primrec₂ pred) :
    Primrec₂ (fun (args : α) (xs : List β) => xs.filter (pred args)) := by
  apply (Primrec.list_foldr Primrec.snd (Primrec.const [])
    (Primrec.cond (hp.comp (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂).of_eq
  intro p
  induction p.2 with
  | nil => rfl
  | cons x xs ih =>
      simp only [List.foldr_cons, List.filter_cons, cond_eq_ite] at ih ⊢
      rw [ih]
#print axioms filter_primitive

theorem isHead_primitive : Primrec₂ isHead :=
  Primrec.and.comp
    (Primrec.and.comp
      (Primrec.beq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1))
      (Primrec.beq.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)) Primrec.fst))
    (Primrec.eq.comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.const (0 : Int))).decide
#print axioms isHead_primitive

theorem headCoefficient_primitive : Primrec₂ headCoefficient := by
  have he : Primrec (fun p : (Nat × RowData) × EntryData =>
      if isHead p.1.1 p.2.2 then p.2.1 else 0) :=
    Primrec.ite (Primrec.eq.comp
      (isHead_primitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.snd))
      (Primrec.const true)) (Primrec.fst.comp Primrec.snd) (Primrec.const 0)
  exact sum_int_primitive.comp (Primrec.list_map (Primrec.snd.comp Primrec.snd) he.to₂)
#print axioms headCoefficient_primitive

theorem remainingOccurrences_primitive : Primrec₂ remainingOccurrences :=
  (filter_primitive (Primrec.not.comp
    (isHead_primitive.comp Primrec.fst (Primrec.snd.comp Primrec.snd))).to₂).comp
      Primrec.fst (Primrec.snd.comp Primrec.snd)
#print axioms remainingOccurrences_primitive

theorem mass_primitive : Primrec mass :=
  sum_nat_primitive.comp (Primrec.list_map Primrec.snd
    (IntegerAlgorithms.Proof.abs_primitive.comp (Primrec.fst.comp Primrec.snd)).to₂)
#print axioms mass_primitive

theorem absoluteConstant_primitive : Primrec absoluteConstant :=
  BlockRowSubstitutionCodeProof.add_primitive.comp
    (subtract_primitive.comp (Primrec.fst.comp Primrec.fst) (Primrec.snd.comp Primrec.fst))
    (subtract_primitive.comp (Primrec.snd.comp Primrec.fst) (Primrec.fst.comp Primrec.fst))
#print axioms absoluteConstant_primitive

theorem center_primitive : Primrec₂ DominantBoundary.Code.center :=
  BlockRowSubstitutionCodeProof.add_primitive.comp
    ((unary_primitive 10 8).comp ((binary_primitive 10 5).comp Primrec.fst
      (subtract_primitive.comp
        (BlockRowSubstitutionCodeProof.multiply_primitive.comp (Primrec.const 2) Primrec.snd)
        (Primrec.const 10)))) (Primrec.const 10)
#print axioms center_primitive

theorem boundary_primitive : Primrec₂ boundary :=
  center_primitive.comp (IntegerAlgorithms.Proof.abs_primitive.comp headCoefficient_primitive)
    (absoluteConstant_primitive.comp Primrec.snd)
#print axioms boundary_primitive

theorem residueRow_primitive : Primrec (fun p : Nat × (Nat × RowData) => residueRow p.1 p.2.1 p.2.2) := by
  let C := Nat × (Nat × RowData)
  have hr : Primrec (fun p : C => p.2.2) := Primrec.snd.comp Primrec.snd
  have hc : Primrec (fun p : C => headCoefficient p.2.1 p.2.2) :=
    headCoefficient_primitive.comp (Primrec.fst.comp Primrec.snd) hr
  have hf : Primrec (fun p : C => WindowCode.numeral (fastControlResidue (p.1 + 1))) :=
    numeral_primitive.comp (fastControlResiduePrimitiveRecursive.comp
      (Primrec.nat_add.comp Primrec.fst (Primrec.const 1)))
  exact ((BlockRowSubstitutionCodeProof.add_primitive.comp (Primrec.fst.comp (Primrec.fst.comp hr))
    (BlockRowSubstitutionCodeProof.multiply_primitive.comp
      (BlockRowSubstitutionCodeProof.toNat_primitive.comp hc) hf)).pair
    (BlockRowSubstitutionCodeProof.add_primitive.comp (Primrec.snd.comp (Primrec.fst.comp hr))
      (BlockRowSubstitutionCodeProof.multiply_primitive.comp
        (BlockRowSubstitutionCodeProof.toNat_primitive.comp
          (IntegerAlgorithms.Proof.negate_primitive.comp hc)) hf))).pair
    (remainingOccurrences_primitive.comp (Primrec.fst.comp Primrec.snd) hr)
#print axioms residueRow_primitive

theorem residueAtom_primitive : Primrec (fun p : Nat × (Nat × RowData) => residueAtom p.1 p.2.1 p.2.2) :=
  divisible_primitive.comp Primrec.fst residueRow_primitive
#print axioms residueAtom_primitive

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
