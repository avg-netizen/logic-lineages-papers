module
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeTargets
public import LogicLineages.OrdinalComparison.SourceMachineSpineCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceMachineQueryCode.Proof

theorem pack_primitive : Primrec pack := Primrec.encode
theorem unpack_primitive : Primrec unpack := Primrec.decode

theorem request_primitive : Primrec₂ request := by
  have hn : Primrec (fun p : Nat×Nat => 4+(SourceMachineSpineCode.compiled p.1 p.2).1) :=
    Primrec.nat_add.comp (Primrec.const 4) (Primrec.fst.comp SourceMachineSpineCode.Proof.uniformPrimitiveRecursive.2.2.2.1)
  have ha : Primrec (fun p : Nat×Nat => SourceMachineSpineCode.aggregate p.1 p.2) :=
    SourceMachineSpineCode.Proof.uniformPrimitiveRecursive.2.2.2.2
  exact hn.pair ((Primrec.snd.comp ha).pair (Primrec.fst.comp ha))

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨pack_primitive,unpack_primitive,request_primitive,pack_primitive.comp request_primitive⟩
end LogicLineages.OrdinalComparison.Source.SourceMachineQueryCode.Proof
