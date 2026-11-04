module
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeTargets
public import LogicLineages.OrdinalComparison.SourceBinarySpineCodeProgramsProof
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.Proof
open SourcePlanSpineCode

theorem constant_primitive : Primrec₂ constant :=
  Primrec.list_cons.comp (Primrec.const ((4,0,0,0) : Instruction))
    (SourceBinarySpineCode.Proof.build_primitive.comp (Primrec.fst.pair ((Primrec.const 1).pair Primrec.snd)))

theorem tail_primitive : Primrec tail :=
  Primrec.list_cons.comp (Primrec.const ((2,10,10,1) : Instruction))
    (Primrec.list_cons.comp (Primrec.const ((2,1,9,2) : Instruction))
      (SourceScalingSpineCode.Proof.build_primitive.comp (Primrec.id.pair ((Primrec.const 2).pair ((Primrec.const 3).pair (Primrec.const remainder))))))
attribute [local irreducible] constant tail

theorem code_primitive : Primrec₂ code := by
  have hc : Primrec (fun p : Nat×Nat => 2*p.1+5) :=
    Primrec.nat_add.comp (Primrec.nat_mul.comp (Primrec.const 2) Primrec.fst) (Primrec.const 5)
  have hi : Primrec (fun p : Nat×Nat => List.replicate 6 ((4,0,0,0) : Instruction) ++ tail p.2) := Primrec.list_append.comp (Primrec.const (List.replicate 6 ((4,0,0,0) : Instruction))) (tail_primitive.comp Primrec.snd)
  exact constant_primitive.comp hc (constant_primitive.comp (Primrec.const 4) (constant_primitive.comp (Primrec.const 1) hi))

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨constant_primitive,tail_primitive,code_primitive,
    SourcePlanSpineCode.Proof.run_primitive.comp code_primitive,
    SourcePlanSpineCode.Proof.uniformPrimitiveRecursive.2.2.comp code_primitive⟩
end LogicLineages.OrdinalComparison.Source.SourceMachineSpineCode.Proof
