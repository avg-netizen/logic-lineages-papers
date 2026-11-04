module
public import LogicLineages.OrdinalComparison.SourceScalingSpineCodeTargets
public import LogicLineages.OrdinalComparison.SourcePlanInsertionCodeProgramsProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceScalingSpineCode.Proof
open SourcePlanSpineCode SourcePrimitiveForestCode
attribute [local irreducible] shiftPort SourcePlanInsertionCode.insert

theorem advance_primitive : Primrec advance := by
  have ha : Primrec (fun s : ScaleState => shiftPort 1 s.1) :=
    SourcePrimitiveForestCode.Proof.shift_primitive.comp (Primrec.const 1) Primrec.fst
  have hb : Primrec (fun s : ScaleState => shiftPort 1 s.2.1) :=
    SourcePrimitiveForestCode.Proof.shift_primitive.comp (Primrec.const 1) (Primrec.fst.comp Primrec.snd)
  have hi : Primrec (fun s : ScaleState => SourcePlanInsertionCode.insert 0 1 s.2.2) :=
    SourcePlanInsertionCode.Proof.insert_primitive.comp ((Primrec.const 0).pair ((Primrec.const 1).pair (Primrec.snd.comp Primrec.snd)))
  exact ha.pair ((Primrec.const 1).pair (Primrec.list_cons.comp
    ((Primrec.const 2).pair ((Primrec.const 1).pair ((Primrec.const 1).pair hb))) hi))
attribute [local irreducible] advance

theorem build_primitive : Primrec (fun p : Nat×Nat×Nat×List Instruction => build p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  have hi : Primrec (fun p : Nat×Nat×Nat×List Instruction => advance^[p.1] p.2) :=
    Primrec.nat_iterate Primrec.fst Primrec.snd (advance_primitive.comp Primrec.snd).to₂
  have hp : Primrec (fun p : Nat×Nat×Nat×List Instruction => List.replicate p.1 ((4,0,0,0) : Instruction)) :=
    (Primrec.list_map (Primrec.list_range.comp Primrec.fst) (Primrec.const ((4,0,0,0) : Instruction)).to₂).of_eq (fun p => by simp)
  have he := (Primrec.const 1).pair ((Primrec.fst.comp hi).pair
    ((Primrec.fst.comp (Primrec.snd.comp hi)).pair (Primrec.const 0)))
  exact Primrec.list_append.comp hp (Primrec.list_cons.comp he (Primrec.snd.comp (Primrec.snd.comp hi)))

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive := ⟨advance_primitive,build_primitive⟩
end LogicLineages.OrdinalComparison.Source.SourceScalingSpineCode.Proof
