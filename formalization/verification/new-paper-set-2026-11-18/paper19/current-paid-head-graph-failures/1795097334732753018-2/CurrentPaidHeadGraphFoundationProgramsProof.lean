module
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphParametersProof
public import LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraphRayProof
public import LogicLineages.ControlSensitivityCurrent.CurrentDecisionCodePrimitiveProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAnnotationMarkerProgramsProof
public import LogicLineages.ControlSensitivityCurrent.RawSourceDAGOperationsPrimitiveProof
public import LogicLineages.StandardControlCurrent.PolicyAssignmentRunPrograms
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
open LogicLineages.OrdinalComparison LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum ForwardTranslation

private abbrev S := List Nat
private abbrev A := S × Nat
private abbrev P := S × Nat × Nat

theorem countProgram : Primrec groundCount :=
  Primrec.list_length.comp (Primrec.listFilter (Primrec.eq.comp Primrec.id (Primrec.const 0)))

theorem replicateZero : Primrec (fun n : Nat => List.replicate n (0 : Nat)) := by
  have h : Primrec (fun n : Nat => (List.range n).map (fun _ => (0 : Nat))) :=
    Primrec.list_map Primrec.list_range (Primrec.const 0).to₂
  exact h.of_eq (fun n => by simp)

private theorem contextProgram : Primrec freshContext :=
  Primrec.list_append.comp (replicateZero.comp countProgram) Primrec.id

private theorem tableProgram : Primrec freshTable := by
  have g : Primrec (fun q : S×Nat => q.1) := Primrec.fst
  have i : Primrec (fun q : S×Nat => q.2) := Primrec.snd
  have h := (Primrec.list_getD 1).comp g i
  have hrow : Primrec (fun q : S×Nat => if q.1.getD q.2 1=0 then groundCount (q.1.take q.2)
      else groundCount q.1+q.2) :=
    Primrec.ite (Primrec.eq.comp h (Primrec.const 0))
      (countProgram.comp (Primrec.list_take.comp i g)) (Primrec.nat_add.comp (countProgram.comp g) i)
  exact Primrec.list_map (Primrec.list_range.comp Primrec.list_length) hrow.to₂

private theorem auxiliaryPackage : Primrec (fun q : A × RawSourceDAG.Code =>
    let ctx := freshContext q.1.1
    let R := RawSourceDAG.Operations.renameCode ctx (freshTable q.1.1) q.2
    let closed := GroundCaptureClosingCode.sourceCode ctx 0 (CurrentTreeCode.expand R)
    (0 :: ctx,8*Nat.pair (ContextInsertionCode.sourceCode 0 1 closed) 0+5)) := by
  let X := A × RawSourceDAG.Code
  have g : Primrec (fun q : X => q.1.1) := Primrec.fst.comp Primrec.fst
  have d : Primrec (fun q : X => q.2) := Primrec.snd
  have ctx := contextProgram.comp g
  have r := RawSourceDAG.Operations.primitive.2.2.2.comp (ctx.pair ((tableProgram.comp g).pair d))
  have e := CurrentTreeCode.effective.comp r
  have c := GroundCaptureClosingCode.StatementChecks.primitive_recursive_algorithms.1.comp
    (ctx.pair ((Primrec.const 0).pair e))
  have w := ContextInsertionCode.StatementChecks.primitive_recursive_algorithms.1.comp
    ((Primrec.const 0).pair ((Primrec.const 1).pair c))
  have app := Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 8)
    (Primrec₂.natPair.comp w (Primrec.const 0))) (Primrec.const 5)
  exact (Primrec.list_cons.comp (Primrec.const 0) ctx).pair app

private theorem auxiliaryProgram : Computable (fun q : A => auxiliaryCode q.1 q.2) := by
  have h := CurrentTreeInputCoverage.StatementChecks.actual_raw_program.2
  apply (Computable.option_map h auxiliaryPackage.to_comp.to₂).of_eq
  intro x
  unfold auxiliaryCode
  rw [Option.map_eq_bind]
  rfl

private theorem shiftProgram : Primrec₂ shiftCode := by
  have h := encodedNaturalProductPrimitiveRecursive.comp
    (Primrec.const CurrentOrdinalEvaluation.omegaCode)
    (encodedKernelBuildersPrimitiveRecursive.1.comp (Primrec.snd : Primrec fun q : Nat×Nat => q.2))
  exact encodedNaturalSumPrimitiveRecursive.comp Primrec.fst h

private theorem scalarCodeProgram (f : Nat → Nat) (hc : Computable f)
    (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (fun q => encodedFiniteValue (CurrentOrdinalEvaluation.evaluate f [] (UnitHeadCode.unitCode q))) := by
  have hfin : Primrec encodedFiniteValue := Primrec.nat_iff.mpr encodedFiniteAlgorithmsPrimitiveRecursive.2
  have harg : Primrec (fun n : Nat => (([] : S),UnitHeadCode.unitCode n)) :=
    (Primrec.const []).pair UnitHeadCode.Proof.primitiveRecursiveAlgorithms.1
  exact hfin.to_comp.comp ((CurrentOrdinalEvaluation.effective f hc hf).comp harg.to_comp)

private abbrev Loaded := P × S
private abbrev HeadLoaded := Loaded × Nat
private abbrev WithScalar := HeadLoaded × Nat

private def finishParams (f : Nat → Nat) (q : WithScalar) : Option ParameterCode :=
  (UnitHeadCode.positiveCode q.1.2).map fun a =>
    let b := encodedClosedHead a
    (b,shiftCode b q.1.1.1.2.2,encodedFiniteValue (CurrentOrdinalEvaluation.evaluate f [] (UnitHeadCode.unitCode q.2)))

private theorem finishProgram (f : Nat → Nat) (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (finishParams f) := by
  have a : Primrec (fun q : WithScalar => q.1.2) := Primrec.snd.comp Primrec.fst
  have k : Primrec (fun q : WithScalar => q.1.1.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)))
  have a' := UnitHeadCode.Proof.primitiveRecursiveAlgorithms.2.1.comp a
  let U := WithScalar × Nat
  have b : Primrec (fun q : U => encodedClosedHead q.2) := encodedClosedHeadPrimitiveRecursive.comp Primrec.snd
  have sk := shiftProgram.comp b (k.comp Primrec.fst)
  have z : Computable (fun q : U => encodedFiniteValue (CurrentOrdinalEvaluation.evaluate f []
      (UnitHeadCode.unitCode q.1.2))) :=
    (scalarCodeProgram f hc hf).comp (Computable.snd.comp Computable.fst)
  exact Computable.option_map a'.to_comp (b.to_comp.pair (sk.to_comp.pair z)).to₂

private def fromVector (f : Nat → Nat) (q : Loaded) : Option ParameterCode :=
  q.2[1]?.bind fun h => q.2[0]?.bind fun z => finishParams f ((q,h),z)

private theorem vectorProgram (f : Nat → Nat) (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (fromVector f) := by
  have hz : Primrec (fun q : HeadLoaded => q.1.2[0]?) :=
    Primrec.list_getElem?.comp (Primrec.snd.comp Primrec.fst) (Primrec.const 0)
  have hh : Primrec (fun q : Loaded => q.2[1]?) := Primrec.list_getElem?.comp Primrec.snd (Primrec.const 1)
  exact Computable.option_bind hh.to_comp (Computable.option_bind hz.to_comp (finishProgram f hc hf).to₂).to₂

private theorem parameterProgram (p : Policy) (hp : PolicyShape.Effective p) (f : Nat → Nat)
    (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (fun q : P => parameterCode p f q.1 q.2.1 q.2.2) := by
  have g : Primrec (fun q : P => q.1) := Primrec.fst
  have a : Primrec (fun q : P => q.2.1) := Primrec.fst.comp Primrec.snd
  have hcheck : PrimrecPred (fun q : P => SyntaxCode.check q.1 q.2.1 = some
      (SyntaxCode.typeCode (Ty.curriedGround 1))) :=
    Primrec.eq.comp (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp (g.pair a)) (Primrec.const _)
  have ha : Computable (fun q : P => PolicyAssignment.assignmentCode p q.1 q.2.1) :=
    (PolicyAssignmentRunPrograms.assignment p hp).comp (g.pair a).to_comp
  have program := CurrentGroundAnnotationPrograms.chooseProgram hcheck
    (Computable.option_bind ha (vectorProgram f hc hf).to₂) (Computable.const none)
  apply program.of_eq
  intro q
  unfold parameterCode fromVector finishParams
  simp only [Option.map_eq_bind,bind,Option.bind_some,pure]

theorem valueProgram (f : Nat → Nat) (hc : Computable f) (hf : FullAddition.Targets.SourceGrowth f) :
    Computable (fun q : Nat×Nat => valueCode f q.1 q.2) := by
  have n : Primrec rawNormCode := Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive
  have v := encodedFiniteTailPrimitiveRecursive.comp (Primrec.fst : Primrec fun q : Nat×Nat => q.1)
    (Primrec.nat_sub.comp Primrec.snd (n.comp Primrec.fst))
  have hm := (FullAddition.completeAddition.2.2.2 f hf).1
  exact (PermittedControl.evaluator_computable f hc hm hf.1).comp v.to_comp

theorem effectivePrefixData : Targets.EffectivePrefixData :=
  ⟨auxiliaryProgram,fun p hp f hc hf => ⟨parameterProgram p hp f hc hf,valueProgram f hc hf⟩⟩

end LogicLineages.ControlSensitivityCurrent.CurrentPaidHeadGraph
