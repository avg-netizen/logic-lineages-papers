module
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescentTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedAffineCodeProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedSourceAdapterProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof
@[expose] public section

namespace LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent.Proof
open CommonHeadCompiler (Instruction)

attribute [local irreducible] Nat.sqrt Nat.unpair rawNormCode
  BalancedAffineCode.numeral BalancedSourceAdapter.lowerCertificate
  BalancedSourceAdapter.termCodes BalancedSourceAdapter.formulaCode

private theorem numeral_primitive :
    Primrec (fun p : List Nat × Nat => BalancedAffineCode.numeral p.1 p.2) :=
  BalancedAffineCode.Proof.uniformPrimitiveRecursive.1

private theorem labelCode_primitive :
    Primrec (fun p : List Nat × List Nat × Nat => labelCode p.1 p.2.1 p.2.2) :=
  Primrec.option_getD.comp
    (Primrec.list_getElem?.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd))
    (numeral_primitive.comp (Primrec.fst.pair (Primrec.const 0)))

attribute [local irreducible] labelCode

private theorem child_primitive :
    Primrec (fun p : List Nat × Nat × List Nat × Instruction =>
      child p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let D := List Nat × Nat × List Nat × Instruction
  have hshape : Primrec (fun p : D => p.1) := Primrec.fst
  have hc : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hlabels : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hq : Primrec (fun p : D => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have ht : Primrec (fun p : D => p.2.2.2.1) := Primrec.fst.comp hq
  have hx : Primrec (fun p : D => p.2.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp hq)
  have hy : Primrec (fun p : D => p.2.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp hq)
  have hleft : Primrec (fun p : D => labelCode p.1 p.2.2.1 p.2.2.2.2.1) :=
    labelCode_primitive.comp (hshape.pair (hlabels.pair hx))
  have hright : Primrec (fun p : D => labelCode p.1 p.2.2.1 p.2.2.2.2.2) :=
    labelCode_primitive.comp (hshape.pair (hlabels.pair hy))
  have hbound : Primrec (fun p : D => BalancedAffineCode.numeral p.1 p.2.2.2.2.1) :=
    numeral_primitive.comp (hshape.pair hx)
  have hzero : Primrec (fun p : D => BalancedAffineCode.numeral p.1 0) :=
    numeral_primitive.comp (hshape.pair (Primrec.const 0))
  have heq : Primrec (fun p : D =>
      (p.1,p.2.1,labelCode p.1 p.2.2.1 p.2.2.2.2.1,
        labelCode p.1 p.2.2.1 p.2.2.2.2.2,(0 : Int))) :=
    hshape.pair (hc.pair (hleft.pair (hright.pair (Primrec.const 0))))
  have hlt : Primrec (fun p : D =>
      (p.1,p.2.1,labelCode p.1 p.2.2.1 p.2.2.2.2.1,
        labelCode p.1 p.2.2.1 p.2.2.2.2.2,(-1 : Int))) :=
    hshape.pair (hc.pair (hleft.pair (hright.pair (Primrec.const (-1)))))
  have hb : Primrec (fun p : D =>
      (p.1,p.2.1,labelCode p.1 p.2.2.1 p.2.2.2.2.2,
        BalancedAffineCode.numeral p.1 p.2.2.2.2.1,(-1 : Int))) :=
    hshape.pair (hc.pair (hright.pair (hbound.pair (Primrec.const (-1)))))
  have hdummy : Primrec (fun p : D =>
      (p.1,p.2.1,BalancedAffineCode.numeral p.1 0,
        BalancedAffineCode.numeral p.1 0,(0 : Int))) :=
    hshape.pair (hc.pair (hzero.pair (hzero.pair (Primrec.const 0))))
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) heq
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) hlt
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 4)) hb hdummy))

attribute [local irreducible] child

private theorem children_primitive :
    Primrec (fun p : List Nat × Nat × List Nat × Code =>
      children p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let D := List Nat × Nat × List Nat × Code
  have hshape : Primrec (fun p : D => p.1) := Primrec.fst
  have hc : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hlabels : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hcode : Primrec (fun p : D => p.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have hargs : Primrec (fun p : D × Instruction =>
      (p.1.1,p.1.2.1,p.1.2.2.1,p.2)) :=
    (hshape.comp Primrec.fst).pair
      ((hc.comp Primrec.fst).pair ((hlabels.comp Primrec.fst).pair Primrec.snd))
  exact Primrec.list_map hcode (child_primitive.comp hargs).to₂

attribute [local irreducible] children

private theorem instructionCode_primitive : Primrec₂ instructionCode := by
  let D := Instruction × Code
  have ht : Primrec (fun p : D => p.1.1) := Primrec.fst.comp Primrec.fst
  have hresult : Primrec (fun p : D => p.2) := Primrec.snd
  have hnegative : Primrec (fun p : D => p.2 ++ [(5,0,0)]) :=
    Primrec.list_append.comp hresult (Primrec.const [(5,0,0)])
  have hsingle : Primrec (fun p : D => [p.1]) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.const [])
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) hresult
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) hresult
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 4)) hnegative hsingle))

attribute [local irreducible] instructionCode

private theorem assemble_primitive : Primrec₂ assemble :=
  Primrec.list_flatten.comp
    (CommonHeadCode.Program.zipWith_primitive instructionCode instructionCode_primitive)

attribute [local irreducible] assemble

private theorem adapterAssemble_primitive :
    Primrec (fun p : Nat × List Nat × Nat × Nat × Nat × Int =>
      BalancedSourceAdapter.assemble p.1 p.2.1 p.2.2.1 p.2.2.2.1
        p.2.2.2.2.1 p.2.2.2.2.2) := by
  rcases BalancedSourceAdapter.Proof.uniformPrimitiveRecursive with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h⟩
  exact h

private theorem adapterFormula_primitive :
    Primrec (fun p : Nat × Nat × Nat × Int =>
      BalancedSourceAdapter.formulaCode p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  rcases BalancedSourceAdapter.Proof.uniformPrimitiveRecursive with
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, h, _⟩
  exact h

private theorem sourceChildren_primitive :
    Primrec (fun p : Nat × List Nat × Nat × Nat × Nat × Int =>
      sourceChildren p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2.1 p.2.2.2.2.2) :=
  children_primitive.comp
    ((Primrec.fst.comp Primrec.snd).pair adapterAssemble_primitive)

private theorem sourceAssemble_primitive :
    Primrec (fun p : Nat × Nat × Nat × Int × List Code =>
      sourceAssemble p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let D := Nat × Nat × Nat × Int × List Code
  have hk : Primrec (fun p : D => p.1) := Primrec.fst
  have he : Primrec (fun p : D => p.2.1) := Primrec.fst.comp Primrec.snd
  have hf : Primrec (fun p : D => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hd : Primrec (fun p : D => p.2.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hresults : Primrec (fun p : D => p.2.2.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))
  have hformula : Primrec (fun p : D =>
      BalancedSourceAdapter.formulaCode p.1 p.2.1 p.2.2.1 p.2.2.2.1) :=
    adapterFormula_primitive.comp (hk.pair (he.pair (hf.pair hd)))
  exact assemble_primitive.comp hformula hresults

private theorem measure_primitive : Primrec measure :=
  Primrec.list_length.comp Primrec.fst

/-- Uniform programs use the actual balanced numeral and source adapter,
including all malformed-input defaults and every original instruction. -/
theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨labelCode_primitive, child_primitive, children_primitive,
    instructionCode_primitive, assemble_primitive, sourceChildren_primitive,
    sourceAssemble_primitive, measure_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.BalancedGuardDescent.Proof
