module
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.PrefixProgramsProof
public import LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.FrameProgramsProof
public import LogicLineages.OrdinalComparison.RankedWordDecisionCompletion.OutcomeTransportProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodePrograms
open PolynomialGraphCompletion WordLinearDecisionCompletion RankedWordDecisionCompletion
open LayeredComparison.SnyatkovCompletion
attribute [local irreducible] Computable Partrec Nat.sqrt Nat.unpair

theorem matrix_computable : Computable (fun p : Nat × Nat × Nat =>
    Code.matrix p.1 p.2.1 p.2.2) :=
  OutcomeTransportPrograms.compile_computable.comp
    (Computable.fst.pair ((Computable.fst.comp Computable.snd).pair
      (residue_primitive.to_comp.comp (Computable.snd.comp Computable.snd))))

theorem commonTail_computable : Computable (fun p : Nat × Nat × Nat =>
    Code.commonTail p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Nat
  have hc : Computable (fun p : A => p.2.2) := Computable.snd.comp Computable.snd
  have hn := names_primitive.to_comp.comp hc
  have hm : Computable₂ (fun p : A => fun maximum : Nat => (Code.matrix p.1 maximum p.2.2).1) :=
    Computable.fst.comp (matrix_computable.comp
      ((Computable.fst.comp Computable.fst).pair
        (Computable.snd.pair (hc.comp Computable.fst))))
  have hmax := AlgorithmPrograms.foldMax_primitive.to_comp.comp
    (AlgorithmPrograms.computable_map 0 hn hm)
  exact Primrec.nat_max.to_comp.comp (Computable.fst.comp Computable.snd)
    (Primrec.nat_max.to_comp.comp (OutcomeTransportPrograms.originalTail_primitive.to_comp.comp hc)
      (Primrec.nat_max.to_comp.comp (residueTail_primitive.to_comp.comp hc) hmax))

/- Compose accepted numeric programs without unfolding their implementations. -/
attribute [local irreducible] Code.matrix Code.commonTail Code.frame
  WordLinearDecisionCompletion.Code.eliminate

theorem high_computable : Computable (fun p : Nat × Nat × Nat =>
    Code.highChildren p.1 p.2.1 p.2.2) := by
  let A := Nat × Nat × Nat
  let B := A × Nat
  have hN : Computable (fun p : B => p.1.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.fst)
  have hc : Computable (fun p : B => p.1.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hmatrix : Computable (fun p : B => Code.matrix p.1.1 p.2 p.1.2.2) :=
    matrix_computable.comp ((Computable.fst.comp Computable.fst).pair
      (Computable.snd.pair hc))
  have hframe : Computable (fun p : B => Code.frame p.1.2.1 p.2 (Code.names p.1.2.2)) :=
    frame_primitive.to_comp.comp (hN.pair (Computable.snd.pair (names_primitive.to_comp.comp hc)))
  have hbody : Computable (fun p : B × Nat =>
      LinearRows.Code.conjunction (Code.frame p.1.1.2.1 p.1.2 (Code.names p.1.1.2.2)) p.2) :=
    AlgorithmPrograms.conjunction_encode_primitive.to_comp.comp
      (hframe.comp Computable.fst) Computable.snd
  have hchild : Computable₂ (fun p : B => fun q : Nat =>
      (p.1.2.1,WordLinearDecisionCompletion.Code.eliminate p.2
        (LinearRows.Code.conjunction (Code.frame p.1.2.1 p.2 (Code.names p.1.2.2)) q))) :=
    (hN.comp Computable.fst).pair
      (WordLinearDecisionCompletion.Proof.actualNumericProgram.to_comp.comp
        (Computable.snd.comp Computable.fst) hbody)
  have hinner := AlgorithmPrograms.computable_map 0 (Computable.snd.comp hmatrix) hchild
  exact computable_flatMap 0
    (names_primitive.to_comp.comp (Computable.snd.comp Computable.snd)) hinner.to₂

theorem children_computable : Computable (fun p : Nat × Nat × Nat =>
    Code.children p.1 p.2.1 p.2.2) := by
  have hcode : Computable (fun p : Nat × Nat × Nat => p.2.2) :=
    Computable.snd.comp Computable.snd
  have hl := prefix_computable.comp
    ((Computable.fst.comp Computable.snd).pair (commonTail_computable.pair hcode))
  have hh := high_computable.comp (Computable.fst.pair (commonTail_computable.pair hcode))
  exact Primrec.list_append.to_comp.comp hl hh

theorem actualNumericPrograms : BranchTargets.ActualNumericPrograms :=
  ⟨variables_primitive,names_primitive,residue_primitive,residueTail_primitive,
    commonTail_computable,children_computable⟩

#print axioms matrix_computable
#print axioms commonTail_computable
#print axioms high_computable
#print axioms children_computable
#print axioms actualNumericPrograms

end LogicLineages.OrdinalComparison.ClosedWordDecisionCompletion.CodePrograms
