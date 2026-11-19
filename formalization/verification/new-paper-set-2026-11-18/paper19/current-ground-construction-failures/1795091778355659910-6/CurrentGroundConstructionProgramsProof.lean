module
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundConstructionTargets
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundBudgetBoxProof
public import LogicLineages.ControlSensitivityCurrent.CurrentGroundAccountProgramsProof
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodePrimitiveProof
@[expose] public section
namespace LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction

open LogicLineages.OrdinalComparison.Source
open LogicLineages.StandardControlCurrent
open AdmissibleSum
open NumericUnaryChain (RawOperator)
open CurrentGroundAnnotationPrograms (chooseProgram)

private abbrev P := List Nat × Nat × Nat
private abbrev S := List Nat × List RawOperator
private abbrev A := List Nat × Nat × Nat × Nat
private abbrev D := List Nat × List RawOperator × Nat
private abbrev Q := A × D × Nat
private abbrev O := (List Nat × Nat × List Nat) × Nat × Nat

private theorem callerVectorProgram (pol : Policy) (hp : PolicyShape.Effective pol) :
    Computable (fun q : P × Nat => do
      let sat := NumericCarrierData.saturateSource (q.2-1) q.1.2.2
      let v ← PolicyAssignment.assignmentCode pol q.1.1 sat
      pure (([],sat,v) : RawOperator)) := by
  have hctx : Primrec (fun q : P×Nat => q.1.1) := Primrec.fst.comp Primrec.fst
  have hsrc : Primrec (fun q : P×Nat => q.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hr : Primrec (fun q : P×Nat => q.2-1) := Primrec.nat_sub.comp Primrec.snd (Primrec.const 1)
  have hs := NumericCarrierData.Proof.primitiveRecursiveAlgorithms.2.2.1.comp hr hsrc
  have hu := (PolicyAssignmentRunPrograms.assignment pol hp).comp (hctx.pair hs).to_comp
  have hs' : Primrec (fun q : (P×Nat)×List Nat =>
      (([] : List Nat), NumericCarrierData.saturateSource (q.1.2-1) q.1.1.2.2,q.2)) :=
    (Primrec.const ([] : List Nat)).pair ((hs.comp Primrec.fst).pair Primrec.snd)
  have h := Computable.option_map hu hs'.to_comp.to₂
  apply h.of_eq
  intro q
  simp [Option.map_eq_bind]

theorem callerProgram (pol : Policy) (hp : PolicyShape.Effective pol) :
    Computable (fun z : List Nat × Nat × Nat => callerCode pol z.1 z.2.1 z.2.2) := by
  have ha : Computable (fun q : P => (TrackedSourceInspectionCode.arityCode q.2.1).bind (fun r =>
      if r=0 then none else
        let sat := NumericCarrierData.saturateSource (r-1) q.2.2
        (PolicyAssignment.assignmentCode pol q.1 sat).bind (fun v => some ([],sat,v)))) :=
    Computable.option_bind
      (TrackedSourceInspectionCode.Proof.primitiveRecursiveAlgorithms.2.comp (Primrec.fst.comp Primrec.snd)).to_comp
      (chooseProgram (Primrec.eq.comp Primrec.snd (Primrec.const 0))
        (Computable.const none) (callerVectorProgram pol hp)).to₂
  have hctx : Primrec (fun q : P => q.1) := Primrec.fst
  have hs : Primrec (fun q : P => q.2.1) := Primrec.fst.comp Primrec.snd
  have hn : Primrec (fun q : P => q.2.2) := Primrec.snd.comp Primrec.snd
  have h := Computable.option_bind
    (SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp (hctx.pair hn)).to_comp
    (chooseProgram (Primrec.eq.comp Primrec.snd (hs.comp Primrec.fst))
      (ha.comp Computable.fst) (Computable.const none)).to₂
  apply h.of_eq
  intro q
  simp [callerCode]

theorem chainProgram (pol : Policy) (hp : PolicyShape.Effective pol) :
    Computable (fun z : List Nat × List RawOperator => chainCode pol z.1 z.2) := by
  have hn := NumericUnaryChain.Proof.primitiveRecursiveAlgorithms
  have hctx : Primrec (fun z : S => NumericUnaryChain.contextCode z.1 z.2) := hn.1
  have hterms : Primrec (fun z : S => (NumericUnaryChain.mergeData z.2).2.map Prod.fst) :=
    Primrec.list_map (Primrec.snd.comp (hn.2.1.comp Primrec.snd)) (Primrec.fst.comp Primrec.snd).to₂
  have hsrc := hn.2.2.1.comp hterms
  have hu := (PolicyAssignmentRunPrograms.assignment pol hp).comp (hctx.pair hsrc).to_comp
  have hout : Primrec (fun q : S × List Nat =>
    (NumericUnaryChain.contextCode q.1.1 q.1.2,
      NumericUnaryChain.chainCode ((NumericUnaryChain.mergeData q.1.2).2.map Prod.fst),q.2)) :=
    (hctx.comp Primrec.fst).pair ((hsrc.comp Primrec.fst).pair Primrec.snd)
  have h := Computable.option_map hu hout.to_comp.to₂
  apply h.of_eq
  intro q
  simp [chainCode,Option.map_eq_bind]

private def finish (pol : Policy) (q : Q) : Option O := do
  let a ← callerCode pol q.1.1 q.1.2.1 q.1.2.2.2
  let out ← chainCode pol q.1.1 (OriginalScaleCompilerCode.paidCode q.2.2 q.2.1.2.1 a)
  pure (out,q.2.2,gap q.2.2 q.2.1.2.1.length q.2.1.2.2)

private theorem finishProgram (pol : Policy) (hp : PolicyShape.Effective pol) : Computable (finish pol) := by
  have hx : Primrec (fun q : Q => q.2.1.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hc : Primrec (fun q : Q => q.1.1) := Primrec.fst.comp Primrec.fst
  have hs : Primrec (fun q : Q => q.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have ha : Primrec (fun q : Q => q.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hb : Primrec (fun q : Q => q.2.2) := Primrec.snd.comp Primrec.snd
  have hn : Primrec (fun q : Q => q.2.1.2.2) :=
    Primrec.snd.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd))
  have hpkg := OriginalScaleCompilerCode.Proof.primitiveRecursiveAlgorithms
  have hpaid := hpkg.2.1.comp ((hb.comp Primrec.fst).pair ((hx.comp Primrec.fst).pair Primrec.snd))
  have hgap : Primrec (fun q : Q => gap q.2.2 q.2.1.2.1.length q.2.1.2.2) :=
    hpkg.2.2.1.comp (hb.pair (hx.pair hn))
  have hcall := (callerProgram pol hp).comp (hc.pair (hs.pair ha)).to_comp
  have hchain := (chainProgram pol hp).comp ((hc.comp Primrec.fst).pair hpaid).to_comp
  have hout : Primrec (fun q : (Q × RawOperator) × (List Nat × Nat × List Nat) =>
      (q.2,q.1.1.2.2,gap q.1.1.2.2 q.1.1.2.1.2.1.length q.1.1.2.1.2.2)) :=
    Primrec.snd.pair ((hb.comp (Primrec.fst.comp Primrec.fst)).pair (hgap.comp (Primrec.fst.comp Primrec.fst)))
  have h := Computable.option_bind hcall (Computable.option_map hchain hout.to_comp.to₂).to₂
  apply h.of_eq
  intro q
  simp [finish,Option.map_eq_bind]

theorem compilerProgram (pol : Policy) (hp : PolicyShape.Effective pol) :
    Computable (fun q : List Nat × Nat × Nat × Nat => compileCode pol q.1 q.2.1 q.2.2.1 q.2.2.2) := by
  have hΓ : Primrec (fun q : A => q.2.1::q.1) :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) Primrec.fst
  have hP : Primrec (fun q : A => q.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hc := SyntaxCode.StatementChecks.checkPrimitiveRecursive.comp (hΓ.pair hP)
  have hocc := TrackedSourceInspectionCode.Proof.primitiveRecursiveAlgorithms.1.comp (Primrec.const 0) hP
  have hs := (CurrentGroundAccountPrograms.sourceProgram pol hp).comp (hΓ.pair hP).to_comp
  have hb := (CurrentGroundBudget.budgetEffective pol hp).comp (hΓ.pair hP).to_comp
  have h := chooseProgram (Primrec.eq.comp hc (Primrec.const (some 0)))
    (chooseProgram (Primrec.eq.comp hocc (Primrec.const true))
      (PolicyPartialMergePrograms.bindTwo hs hb (finishProgram pol hp)) (Computable.const none))
    (Computable.const none)
  apply h.of_eq
  intro q
  simp [compileCode,finish]

theorem algorithmsEffective : CurrentGroundConstructionTargets.AlgorithmsEffective := by
  intro p hp
  exact ⟨callerProgram p hp,chainProgram p hp,compilerProgram p hp⟩

end LogicLineages.ControlSensitivityCurrent.CurrentGroundConstruction
