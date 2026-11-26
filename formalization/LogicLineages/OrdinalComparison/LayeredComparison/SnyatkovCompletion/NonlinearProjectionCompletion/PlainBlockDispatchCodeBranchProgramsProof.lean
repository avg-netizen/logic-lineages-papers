module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeRenameProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockLinearizationCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.TiedLinearCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
open PlainBlockDispatchCode
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

attribute [local irreducible] rename BlockFormulaSubstitutionCode.formula TiedLinearCode.eliminate
attribute [local irreducible] PlainBlockLinearizationCode.cutoff PlainBlockLinearizationCode.frame
attribute [local irreducible] PlainBlockLinearizationCode.outside
attribute [local irreducible] PlainBlockLinearizationCode.bandCandidate

theorem small_computable : Computable₂ small := by
  let A := (List Nat × Nat) × Nat
  have he : Computable (fun p : A × Nat =>
      (p.1.1.1.erase p.1.2, BlockFormulaSubstitutionCode.formula p.1.2 (WindowCode.numeral p.2) p.1.1.2)) :=
    (erase_primitive.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst)).pair
      (BlockFormulaSubstitutionCodeProof.actualFormulaProgram.comp
        ((Computable.snd.comp Computable.fst).pair
          ((PlainBlockLinearizationCodeProof.numeral_primitive.to_comp.comp Computable.snd).pair
            (Computable.snd.comp (Computable.fst.comp Computable.fst)))))
  have hm : Computable (fun p : A =>
      (List.range (PlainBlockLinearizationCode.cutoff p.1.2)).map (fun n =>
        (p.1.1.erase p.2, BlockFormulaSubstitutionCode.formula p.2 (WindowCode.numeral n) p.1.2))) :=
    map_program 0 (Primrec.list_range.to_comp.comp
      (PlainBlockLinearizationCodeProof.cutoff_primitive.to_comp.comp (Computable.snd.comp Computable.fst))) he.to₂
  apply (Computable.option_casesOn
    (Primrec.list_head?.to_comp.comp Computable.fst) (Computable.const []) hm.to₂).of_eq
  rintro ⟨bound, code⟩
  cases bound <;> rfl
#print axioms small_computable

theorem ties_computable : Computable₂ ties := by
  let A := (List Nat × Nat) × Nat
  have hf : Primrec (fun p : A => p.1.1.filter (fun j => j != p.2)) :=
    (PlainBlockLinearizationCodeProof.filter_primitive
      (Primrec.not.comp (Primrec.beq.comp Primrec.snd Primrec.fst)).to₂).comp
      Primrec.snd (Primrec.fst.comp Primrec.fst)
  have he : Computable (fun p : A × Nat =>
      (p.1.1.1.erase p.1.2, rename p.1.2 p.2 p.1.1.2)) :=
    (erase_primitive.to_comp.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))
      (Computable.snd.comp Computable.fst)).pair
      (rename_computable.comp ((Computable.snd.comp Computable.fst).pair
        (Computable.snd.pair (Computable.snd.comp (Computable.fst.comp Computable.fst)))))
  exact flatMap_program 0 Computable.fst (map_program 0 hf.to_comp he.to₂).to₂
#print axioms ties_computable

theorem bandPayload_computable : Computable (fun p : ((List Nat × Nat) × Nat) × Nat =>
    let a := BlockFormulaSubstitutionCode.decodeAtom p.2
    if a.1 = 0 then
      if PlainBlockLinearizationCode.headCoefficient p.1.2 a.2.2 = 0 then [] else
        (List.range 5).map (fun d => (p.1.1.1.erase p.1.2,
          BlockFormulaSubstitutionCode.formula p.1.2
            (PlainBlockLinearizationCode.bandCandidate p.1.2 a.2.2 d) p.1.1.2))
    else []) := by
  let A := ((List Nat × Nat) × Nat) × Nat
  have ha : Primrec (fun p : A => BlockFormulaSubstitutionCode.decodeAtom p.2) :=
    BlockFormulaSubstitutionCodeProof.decodeAtom_primitive.comp Primrec.snd
  have hi : Primrec (fun p : A => p.1.2) := Primrec.snd.comp Primrec.fst
  have hr : Primrec (fun p : A => (BlockFormulaSubstitutionCode.decodeAtom p.2).2.2) :=
    Primrec.snd.comp (Primrec.snd.comp ha)
  have hb : Computable (fun p : A × Nat => PlainBlockLinearizationCode.bandCandidate
      p.1.1.2 (BlockFormulaSubstitutionCode.decodeAtom p.1.2).2.2 p.2) :=
    PlainBlockLinearizationCodeProof.bandCandidate_primitive.to_comp.comp
      ((hi.to_comp.comp Computable.fst).pair
        ((hr.to_comp.comp Computable.fst).pair Computable.snd))
  have he : Computable (fun p : A × Nat =>
      (p.1.1.1.1.erase p.1.1.2, BlockFormulaSubstitutionCode.formula p.1.1.2
        (PlainBlockLinearizationCode.bandCandidate p.1.1.2
          (BlockFormulaSubstitutionCode.decodeAtom p.1.2).2.2 p.2) p.1.1.1.2)) :=
    (erase_primitive.to_comp.comp
      (Computable.fst.comp (Computable.fst.comp (Computable.fst.comp Computable.fst)))
      (hi.to_comp.comp Computable.fst)).pair
      (BlockFormulaSubstitutionCodeProof.actualFormulaProgram.comp
        ((hi.to_comp.comp Computable.fst).pair
          (hb.pair (Computable.snd.comp (Computable.fst.comp (Computable.fst.comp Computable.fst))))))
  exact ite_program (Primrec.eq.comp (Primrec.fst.comp ha) (Primrec.const 0))
    (ite_program (Primrec.eq.comp
      (PlainBlockLinearizationCodeProof.headCoefficient_primitive.comp hi hr) (Primrec.const (0 : Int)))
      (Computable.const []) (map_program 0 (Computable.const (List.range 5)) he.to₂)) (Computable.const [])
#print axioms bandPayload_computable

theorem bands_computable : Computable₂ bands := by
  have hm : Computable (fun p : (List Nat × Nat) × Nat =>
      (LinearRows.Code.atoms p.1.2).flatMap (fun payload =>
        let a := BlockFormulaSubstitutionCode.decodeAtom payload
        if a.1 = 0 then
          if PlainBlockLinearizationCode.headCoefficient p.2 a.2.2 = 0 then [] else
            (List.range 5).map (fun d => (p.1.1.erase p.2,
              BlockFormulaSubstitutionCode.formula p.2
                (PlainBlockLinearizationCode.bandCandidate p.2 a.2.2 d) p.1.2))
        else [])) :=
    flatMap_program 0
      (LinearRowsCodeProof.atoms_primitive.to_comp.comp (Computable.snd.comp Computable.fst))
      bandPayload_computable.to₂
  exact flatMap_program 0 Computable.fst hm.to₂
#print axioms bands_computable

theorem far_computable : Computable₂ far := by
  let A := (List Nat × Nat) × Nat
  have hi : Computable (fun p : A => p.2) := Computable.snd
  have hc : Computable (fun p : A => p.1.2) := Computable.snd.comp Computable.fst
  have hf : Computable (fun p : A => PlainBlockLinearizationCode.frame p.1.1 p.2 p.1.2) :=
    PlainBlockLinearizationCodeProof.frame_primitive.to_comp.comp
      ((Computable.fst.comp Computable.fst).pair (hi.pair hc))
  have hout : Computable (fun p : A => PlainBlockLinearizationCode.outside p.2 p.1.2) :=
    PlainBlockLinearizationCodeProof.outside_primitive.to_comp.comp hi hc
  have hlin : Computable (fun p : A => PlainBlockLinearizationCode.linearize p.2 p.1.2) :=
    PlainBlockLinearizationCodeProof.linearize_primitive.to_comp.comp hi hc
  have hbody := PlainBlockLinearizationCodeProof.conjunction_primitive.to_comp.comp hf
    (PlainBlockLinearizationCodeProof.conjunction_primitive.to_comp.comp hout hlin)
  have he : Computable (fun p : A => (p.1.1.erase p.2, TiedLinearCode.eliminate p.2
      (PlainBlockLinearizationCode.conjunction (PlainBlockLinearizationCode.frame p.1.1 p.2 p.1.2)
        (PlainBlockLinearizationCode.conjunction (PlainBlockLinearizationCode.outside p.2 p.1.2)
          (PlainBlockLinearizationCode.linearize p.2 p.1.2))))) :=
    (erase_primitive.to_comp.comp (Computable.fst.comp Computable.fst) hi).pair
      ((show Computable₂ TiedLinearCode.eliminate from TiedLinearCodeProof.actualEliminationProgram).comp hi hbody)
  exact map_program 0 Computable.fst he.to₂
#print axioms far_computable

attribute [local irreducible] small ties bands far

theorem branches_computable : Computable₂ branches := Computable.list_append.comp
  (Computable.list_append.comp (Computable.list_append.comp small_computable ties_computable)
    bands_computable) far_computable
#print axioms branches_computable

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.NonlinearProjectionCompletion.PlainBlockDispatchCodeProof
