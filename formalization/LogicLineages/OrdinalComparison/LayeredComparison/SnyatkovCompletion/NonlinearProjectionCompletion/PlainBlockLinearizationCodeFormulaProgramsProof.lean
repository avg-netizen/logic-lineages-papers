module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeGuardProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
open PlainBlockLinearizationCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair


theorem atomCharge_primitive : Primrec atomCharge :=
  Primrec.nat_add.comp
    (Primrec.nat_mul.comp (Primrec.const 4) (mass_primitive.comp (Primrec.snd.comp Primrec.snd)))
    (Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0)) (Primrec.const 0)
      (Primrec.nat_add.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 1)))
#print axioms atomCharge_primitive

theorem cutoff_primitive : Primrec cutoff :=
  Primrec.nat_add.comp (Primrec.const 1)
    (sum_nat_primitive.comp (Primrec.list_map LinearRowsCodeProof.atoms_primitive
      (atomCharge_primitive.comp (BlockFormulaSubstitutionCodeProof.decodeAtom_primitive.comp Primrec.snd)).to₂))
#print axioms cutoff_primitive

theorem lowerGuard_primitive : Primrec₂ lowerGuard :=
  nonnegative_primitive.comp (((Primrec.const (WindowCode.numeral 0)).pair
    (numeral_primitive.comp Primrec.snd)).pair
    (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair
      (TiedLinearCodeProof.variableItem_primitive.comp Primrec.fst)) (Primrec.const [])))
#print axioms lowerGuard_primitive

theorem strictMaximumGuard_primitive : Primrec₂ strictMaximumGuard :=
  nonnegative_primitive.comp ((Primrec.const (WindowCode.numeral 0, WindowCode.numeral 1)).pair
    (Primrec.list_cons.comp ((Primrec.const (1 : Int)).pair
      (TiedLinearCodeProof.variableItem_primitive.comp Primrec.fst))
      (Primrec.list_cons.comp ((Primrec.const (-1 : Int)).pair
        (TiedLinearCodeProof.variableItem_primitive.comp Primrec.snd)) (Primrec.const []))))
#print axioms strictMaximumGuard_primitive

theorem frame_primitive : Primrec (fun p : List Nat × (Nat × Nat) => frame p.1 p.2.1 p.2.2) := by
  let C := List Nat × (Nat × Nat)
  have hf : Primrec (fun p : C => p.1.filter (fun j => j != p.2.1)) :=
    (filter_primitive (Primrec.not.comp (Primrec.beq.comp Primrec.snd Primrec.fst)).to₂).comp
      (Primrec.fst.comp Primrec.snd) Primrec.fst
  have he : Primrec (fun p : C × Nat => strictMaximumGuard p.1.2.1 p.2) :=
    strictMaximumGuard_primitive.comp (Primrec.fst.comp (Primrec.snd.comp Primrec.fst)) Primrec.snd
  exact conjunction_primitive.comp
    (lowerGuard_primitive.comp (Primrec.fst.comp Primrec.snd)
      (cutoff_primitive.comp (Primrec.snd.comp Primrec.snd)))
    (all_primitive.comp (Primrec.list_map hf he.to₂))
#print axioms frame_primitive

theorem outside_primitive : Primrec₂ outside := by
  let C := (Nat × Nat) × Nat
  have ha : Primrec (fun p : C => BlockFormulaSubstitutionCode.decodeAtom p.2) :=
    BlockFormulaSubstitutionCodeProof.decodeAtom_primitive.comp Primrec.snd
  have he : Primrec (fun p : C =>
      let a := BlockFormulaSubstitutionCode.decodeAtom p.2
      if a.1 = 0 then outsideRow p.1.1 a.2.2 else 0) :=
    Primrec.ite (Primrec.eq.comp (Primrec.fst.comp ha) (Primrec.const 0))
      (outsideRow_primitive.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp (Primrec.snd.comp ha))) (Primrec.const 0)
  exact all_primitive.comp (Primrec.list_map (LinearRowsCodeProof.atoms_primitive.comp Primrec.snd) he.to₂)
#print axioms outside_primitive

attribute [local irreducible] linearizeNonnegative residueAtom

theorem linearizeAtom_primitive : Primrec₂ linearizeAtom := by
  have hr : Primrec (fun p : Nat × AtomData => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec.ite (Primrec.eq.comp (Primrec.fst.comp Primrec.snd) (Primrec.const 0))
    (linearizeNonnegative_primitive.comp Primrec.fst hr)
    (residueAtom_primitive.comp ((Primrec.fst.comp (Primrec.snd.comp Primrec.snd)).pair
      (Primrec.fst.pair hr)))
#print axioms linearizeAtom_primitive

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProof
