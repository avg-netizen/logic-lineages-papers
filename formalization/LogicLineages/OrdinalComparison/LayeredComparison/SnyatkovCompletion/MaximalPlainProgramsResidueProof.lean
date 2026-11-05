module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsTargets
public import LogicLineages.OrdinalComparison.FixedSeedControlResidueProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.LinearRowsCodeDataProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsProof
open MaximalPlainPrograms
private abbrev Item := Int × NormalForm.Code.ItemData
private abbrev State := Int × List Item

private theorem residueSplit_primitive :
    Primrec (fun p : Nat × Nat × List Item => Code.residueSplit p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × List Item
  let B := A × (Item × State)
  have hi : Primrec (fun p : B => p.1.1) := Primrec.fst.comp Primrec.fst
  have hm : Primrec (fun p : B => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ha : Primrec (fun p : B => p.2.1) := Primrec.fst.comp Primrec.snd
  have hr : Primrec (fun p : B => p.2.2) := Primrec.snd.comp Primrec.snd
  have ht : Primrec (fun p : B => p.2.1.2.1) := Primrec.fst.comp (Primrec.snd.comp ha)
  have hn : Primrec (fun p : B => p.2.1.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp ha))
  have hc : Primrec (fun p : B => (fastControlResidue p.1.2.1 : Int)) :=
    IntegerAlgorithms.Proof.ofNat_primitive.comp
      (FixedSeedControlResidue.Proof.uniformPrimitiveRecursiveData.2.1.comp hm)
  have hsum : Primrec (fun p : B => p.2.1.1 * (fastControlResidue p.1.2.1 : Int) + p.2.2.1) :=
    IntegerAlgorithms.Proof.add_primitive.comp
      (IntegerAlgorithms.Proof.mul_primitive.comp (Primrec.fst.comp ha) hc) (Primrec.fst.comp hr)
  have hs : Primrec (fun p : B => if p.2.1.2.1 = 1 ∧ p.2.1.2.2.1 = p.1.1 then
      (p.2.1.1 * (fastControlResidue p.1.2.1 : Int) + p.2.2.1, p.2.2.2)
      else (p.2.2.1, p.2.1 :: p.2.2.2)) :=
    Primrec.ite ((Primrec.eq.comp ht (Primrec.const 1)).and (Primrec.eq.comp hn hi))
      (hsum.pair (Primrec.snd.comp hr))
      ((Primrec.fst.comp hr).pair (Primrec.list_cons.comp ha (Primrec.snd.comp hr)))
  exact Primrec.list_foldr (Primrec.snd.comp Primrec.snd) (Primrec.const (0, [])) hs.to₂

theorem residueRow_primitive : MaximalPlainProgramsTargets.ActualResidueProgram := by
  let A := Nat × Nat × NormalForm.Code.RowData
  have hr : Primrec (fun p : A => p.2.2) := Primrec.snd.comp Primrec.snd
  have hp : Primrec (fun p : A => Code.residueSplit p.1 p.2.1 p.2.2.2) :=
    residueSplit_primitive.comp (Primrec.fst.pair
      ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp hr)))
  exact (IntegerAlgorithms.Proof.add_primitive.comp (Primrec.fst.comp hr)
    (Primrec.fst.comp hp)).pair (Primrec.snd.comp hp)

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.MaximalPlainProgramsProof
