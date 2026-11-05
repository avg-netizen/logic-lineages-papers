module
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceTargets
public import LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.SourceParameterDecisionProgramsProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProof
open BaseBooleanSource
attribute [local irreducible] Nat.sqrt Nat.unpair

theorem head_primitive : Primrec (fun xs : List Nat => xs.headD 1) := by
  have h : Primrec (fun xs : List Nat => xs.getD 0 1) :=
    (Primrec.list_getD 1).comp Primrec.id (Primrec.const 0)
  apply h.of_eq
  intro xs
  cases xs <;> rfl

theorem step_primitive : Primrec₂ Code.step := by
  let A := CommonHeadCompiler.Instruction × List Nat
  have tag : Primrec (fun p : A => p.1.1) := Primrec.fst.comp Primrec.fst
  have left : Primrec (fun p : A => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have right : Primrec (fun p : A => p.1.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.fst)
  have hd : Primrec (fun p : A => p.2.headD 1) := head_primitive.comp Primrec.snd
  have tl : Primrec (fun p : A => p.2.tail) := Primrec.list_tail.comp Primrec.snd
  have prev : Primrec (fun p : A => p.2.tail.headD 1) := head_primitive.comp tl
  have rest : Primrec (fun p : A => p.2.tail.tail) := Primrec.list_tail.comp tl
  have eqcode := (SourceBooleanProgramsProof.binary_primitive 5 0).comp left right
  have ltcode := (SourceBooleanProgramsProof.binary_primitive 5 1).comp left right
  have bcode := (SourceBooleanProgramsProof.unary_primitive 5 2).comp
    ((SourceBooleanProgramsProof.binary_primitive 5 1).comp right
      (Primrec.nat_mul.comp (Primrec.const 4) left))
  have ncode := (SourceBooleanProgramsProof.unary_primitive 5 2).comp hd
  have ccode := (SourceBooleanProgramsProof.binary_primitive 5 3).comp prev hd
  have dcode := (SourceBooleanProgramsProof.unary_primitive 5 2).comp
    ((SourceBooleanProgramsProof.binary_primitive 5 3).comp
      ((SourceBooleanProgramsProof.unary_primitive 5 2).comp prev)
      ((SourceBooleanProgramsProof.unary_primitive 5 2).comp hd))
  have h := Primrec.ite (Primrec.eq.comp tag (Primrec.const 0))
    (Primrec.list_cons.comp (Primrec.const 1) Primrec.snd)
    (Primrec.ite (Primrec.eq.comp tag (Primrec.const 1))
      (Primrec.list_cons.comp (Primrec.const 0) Primrec.snd)
      (Primrec.ite (Primrec.eq.comp tag (Primrec.const 2))
        (Primrec.list_cons.comp eqcode Primrec.snd)
        (Primrec.ite (Primrec.eq.comp tag (Primrec.const 3))
          (Primrec.list_cons.comp ltcode Primrec.snd)
          (Primrec.ite (Primrec.eq.comp tag (Primrec.const 4))
            (Primrec.list_cons.comp bcode Primrec.snd)
            (Primrec.ite (Primrec.eq.comp tag (Primrec.const 5))
              (Primrec.list_cons.comp ncode tl)
              (Primrec.ite (Primrec.eq.comp tag (Primrec.const 6))
                (Primrec.list_cons.comp ccode rest)
                (Primrec.ite (Primrec.eq.comp tag (Primrec.const 7))
                  (Primrec.list_cons.comp dcode rest)
                  (Primrec.list_cons.comp (Primrec.const 1) Primrec.snd))))))))
  apply h.of_eq
  intro p
  simp only [Code.step, Nat.add_zero]

attribute [local irreducible] Code.step

theorem run_primitive : Primrec₂ Code.run := by
  let A := List CommonHeadCompiler.Instruction × List Nat
  have hs : Primrec (fun p : A × (List Nat × CommonHeadCompiler.Instruction) => Code.step p.2.2 p.2.1) :=
    step_primitive.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_foldl Primrec.fst Primrec.snd hs.to₂

attribute [local irreducible] Code.run

theorem compile_primitive : Primrec Code.compile :=
  head_primitive.comp (run_primitive.comp Primrec.id (Primrec.const []))

attribute [local irreducible] Code.compile

theorem decideExists_primitive : Primrec
    (fun p : List Nat × (List Nat × List CommonHeadCompiler.Instruction) => Code.decideExists p.1 p.2.1 p.2.2) :=
  SourceParameterDecisionProof.decideExists_primitive.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (compile_primitive.comp (Primrec.snd.comp Primrec.snd))))

theorem decideForall_primitive : Primrec
    (fun p : List Nat × (List Nat × List CommonHeadCompiler.Instruction) => Code.decideForall p.1 p.2.1 p.2.2) :=
  SourceParameterDecisionProof.decideForall_primitive.comp
    (Primrec.fst.pair ((Primrec.fst.comp Primrec.snd).pair (compile_primitive.comp (Primrec.snd.comp Primrec.snd))))

theorem decideClosureExists_primitive : Primrec Code.decideClosureExists :=
  SourceBooleanProgramsProof.decideExists_primitive.comp compile_primitive

theorem decideClosureForall_primitive : Primrec Code.decideClosureForall :=
  SourceBooleanProgramsProof.decideForall_primitive.comp compile_primitive

theorem actualNumericPrograms : BaseBooleanSourceTargets.ActualNumericPrograms :=
  ⟨step_primitive, run_primitive, compile_primitive, decideExists_primitive,
    decideForall_primitive, decideClosureExists_primitive, decideClosureForall_primitive⟩

end LogicLineages.OrdinalComparison.LayeredComparison.SnyatkovCompletion.BaseBooleanSourceProof
