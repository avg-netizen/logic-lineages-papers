module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadClosureDecisionCodeInterface
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProgramsProof
public import LogicLineages.OrdinalComparison.LayeredComparison.CommonHeadCodePrimitiveProof
public import LogicLineages.OrdinalComparison.LayeredComparison.BalancedBoxEvaluationGraphProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanProof
open CommonHeadBoolean
attribute [local irreducible] Nat.sqrt Nat.unpair CommonLayerComparison.compileCode

theorem head_primitive : Primrec Code.head := by
  have h : Primrec (fun xs : Code.Stack => xs.getD 0 [(0,0,0)]) :=
    (Primrec.list_getD ([(0,0,0)] : Code.Program)).comp Primrec.id (Primrec.const 0)
  apply h.of_eq
  intro xs
  cases xs <;> rfl

theorem step_computable : Computable (fun p : List Nat × (CommonHeadCompiler.Instruction × Code.Stack) =>
    Code.step p.1 p.2.1 p.2.2) := by
  let A := List Nat × (CommonHeadCompiler.Instruction × Code.Stack)
  have tag : Computable (fun p : A => p.2.1.1) := Computable.fst.comp (Computable.fst.comp Computable.snd)
  have left : Computable (fun p : A => p.2.1.2.1) := Computable.fst.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have right : Computable (fun p : A => p.2.1.2.2) := Computable.snd.comp (Computable.snd.comp (Computable.fst.comp Computable.snd))
  have stack : Computable (fun p : A => p.2.2) := Computable.snd.comp Computable.snd
  have hd := head_primitive.to_comp.comp stack
  have tl := Primrec.list_tail.to_comp.comp stack
  have prev := head_primitive.to_comp.comp tl
  have rest := Primrec.list_tail.to_comp.comp tl
  have eqcode := CommonHeadClosureDecisionSuppliers.allCodeEffectivity.comp
    (Computable.fst.pair (left.pair (right.pair (Computable.const (0 : Int)))))
  have ltcode := CommonHeadClosureDecisionSuppliers.allCodeEffectivity.comp
    (Computable.fst.pair (left.pair (right.pair (Computable.const (-1 : Int)))))
  have ncode := CommonHeadCode.Program.negative_primitive.to_comp.comp hd
  have ccode := CommonHeadCode.Program.conjunction_primitive.to_comp.comp prev hd
  have dcode := CommonHeadCode.Program.disjunction_primitive.to_comp.comp prev hd
  have test (n : Nat) : Computable (fun p : A => decide (p.2.1.1 = n)) :=
    Primrec.eq.decide.to_comp.comp tag (Computable.const n)
  have h := Computable.cond (test 0)
    (Primrec.list_cons.to_comp.comp (Computable.const ([(0,0,0)] : Code.Program)) stack)
    (Computable.cond (test 1)
      (Primrec.list_cons.to_comp.comp (Computable.const ([(1,0,0)] : Code.Program)) stack)
      (Computable.cond (test 2) (Primrec.list_cons.to_comp.comp eqcode stack)
        (Computable.cond (test 3) (Primrec.list_cons.to_comp.comp ltcode stack)
          (Computable.cond (test 5) (Primrec.list_cons.to_comp.comp ncode tl)
            (Computable.cond (test 6) (Primrec.list_cons.to_comp.comp ccode rest)
              (Computable.cond (test 7) (Primrec.list_cons.to_comp.comp dcode rest)
                (Primrec.list_cons.to_comp.comp (Computable.const ([(0,0,0)] : Code.Program)) stack)))))))
  apply h.of_eq
  intro p
  simp only [Bool.cond_decide, Code.step]

attribute [local irreducible] Code.step

theorem run_computable : Computable (fun p : List Nat × (Code.Program × Code.Stack) =>
    Code.run p.1 p.2.1 p.2.2) := by
  let A := List Nat × (Code.Program × Code.Stack)
  have hx : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have hs : Computable (fun p : A => p.2.2) := Computable.snd.comp Computable.snd
  have hstep : Computable₂ (fun p : A => fun state : Code.Stack × CommonHeadCompiler.Instruction =>
      Code.step p.1 state.2 state.1) :=
    step_computable.comp ((Computable.fst.comp Computable.fst).pair
      ((Computable.snd.comp Computable.snd).pair (Computable.fst.comp Computable.snd)))
  exact BalancedBoxEvaluation.Graph.computable_foldl (0,0,0) hx hs hstep

attribute [local irreducible] Code.run

theorem compile_computable : Computable₂ Code.compile :=
  head_primitive.to_comp.comp (run_computable.comp
    (Computable.fst.pair (Computable.snd.pair (Computable.const []))))

attribute [local irreducible] Code.compile

theorem decideExists_computable : Computable (fun p : List Nat × (List Nat × (List Nat × Code.Program)) =>
    Code.decideExists p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := List Nat × (List Nat × (List Nat × Code.Program))
  have hxs : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have hvalues : Computable (fun p : A => p.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hcode : Computable (fun p : A => p.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact BaseBooleanSourceProof.decideExists_primitive.to_comp.comp
    (hxs.pair (hvalues.pair (compile_computable.comp Computable.fst hcode)))

theorem decideForall_computable : Computable (fun p : List Nat × (List Nat × (List Nat × Code.Program)) =>
    Code.decideForall p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := List Nat × (List Nat × (List Nat × Code.Program))
  have hxs : Computable (fun p : A => p.2.1) := Computable.fst.comp Computable.snd
  have hvalues : Computable (fun p : A => p.2.2.1) := Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hcode : Computable (fun p : A => p.2.2.2) := Computable.snd.comp (Computable.snd.comp Computable.snd)
  exact BaseBooleanSourceProof.decideForall_primitive.to_comp.comp
    (hxs.pair (hvalues.pair (compile_computable.comp Computable.fst hcode)))

theorem decideClosureExists_computable : Computable₂ Code.decideClosureExists :=
  BaseBooleanSourceProof.decideClosureExists_primitive.to_comp.comp compile_computable

theorem decideClosureForall_computable : Computable₂ Code.decideClosureForall :=
  BaseBooleanSourceProof.decideClosureForall_primitive.to_comp.comp compile_computable

theorem actualAllCodePrograms : CommonHeadBooleanTargets.ActualAllCodePrograms :=
  ⟨step_computable, run_computable, compile_computable, decideExists_computable,
    decideForall_computable, decideClosureExists_computable, decideClosureForall_computable⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.CommonHeadBooleanProof
