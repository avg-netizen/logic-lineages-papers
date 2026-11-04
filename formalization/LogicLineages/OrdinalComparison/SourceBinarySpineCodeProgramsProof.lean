module
public import LogicLineages.OrdinalComparison.SourceBinarySpineCodeTargets
public import LogicLineages.OrdinalComparison.SourceScalingSpineCodeProgramsProof
public import LogicLineages.OrdinalComparison.SourceBinaryHalvingTraceProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode.Proof
open SourcePlanSpineCode SourcePrimitiveForestCode
attribute [local irreducible] shiftPort SourcePlanInsertionCode.insert

theorem advance_primitive : Primrec (fun p : Nat×BinaryState => advance p.1 p.2) := by
  have hn : Primrec (fun p : Nat×BinaryState => p.2.1) := Primrec.fst.comp Primrec.snd
  have ho : Primrec (fun p : Nat×BinaryState => p.2.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  have hi : Primrec (fun p : Nat×BinaryState => p.2.2.2) := Primrec.snd.comp (Primrec.snd.comp Primrec.snd)
  have h1 := SourcePrimitiveForestCode.Proof.shift_primitive.comp (Primrec.const 1) ho
  have h3 := SourcePrimitiveForestCode.Proof.shift_primitive.comp (Primrec.const 3) ho
  have i1 := SourcePlanInsertionCode.Proof.insert_primitive.comp ((Primrec.const 0).pair ((Primrec.const 1).pair hi))
  have i3 := SourcePlanInsertionCode.Proof.insert_primitive.comp ((Primrec.const 0).pair ((Primrec.const 3).pair hi))
  have c1 := Primrec.list_cons.comp ((Primrec.const 2).pair ((Primrec.const 1).pair ((Primrec.const 1).pair h1))) i1
  have c3 := Primrec.list_cons.comp (Primrec.const ((2,3,3,2) : Instruction))
    (Primrec.list_cons.comp (Primrec.const ((3,1,0,0) : Instruction))
      (Primrec.list_cons.comp ((Primrec.const 2).pair ((Primrec.const 2).pair ((Primrec.const 1).pair h3))) i3))
  exact Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    ((Primrec.nat_add.comp hn (Primrec.const 1)).pair ((Primrec.const 1).pair c1))
    ((Primrec.nat_add.comp hn (Primrec.const 3)).pair ((Primrec.const 3).pair c3))
attribute [local irreducible] advance

theorem terminal_primitive : Primrec₂ terminal :=
  Primrec.ite (Primrec.eq.comp Primrec.fst (Primrec.const 0))
    ((Primrec.const 1).pair (Primrec.snd.pair ((Primrec.const 0).pair (Primrec.const 0))))
    ((Primrec.const 3).pair (Primrec.snd.pair ((Primrec.const 0).pair (Primrec.const 0))))

theorem buildBits_primitive : Primrec (fun p : List Nat×Nat×Nat×List Instruction => buildBits p.1 p.2.1 p.2.2.1 p.2.2.2) := by
  let A := List Nat×Nat×Nat×List Instruction
  have hs : Primrec (fun p : A×(BinaryState×Nat) => advance p.2.2 p.2.1) :=
    advance_primitive.comp ((Primrec.snd.comp Primrec.snd).pair (Primrec.fst.comp Primrec.snd))
  have hf : Primrec (fun p : A => p.1.foldl (fun s b => advance b s) (0,p.2.2.1,p.2.2.2)) :=
    Primrec.list_foldl Primrec.fst ((Primrec.const 0).pair (Primrec.snd.comp (Primrec.snd.comp Primrec.id))) hs.to₂
  have hn := Primrec.fst.comp hf
  have ho := Primrec.fst.comp (Primrec.snd.comp hf)
  have hi := Primrec.snd.comp (Primrec.snd.comp hf)
  have hp : Primrec (fun p : A => List.replicate (p.1.foldl (fun s b => advance b s) (0,p.2.2.1,p.2.2.2)).1 ((4,0,0,0) : Instruction)) :=
    (Primrec.list_map (Primrec.list_range.comp hn) (Primrec.const ((4,0,0,0) : Instruction)).to₂).of_eq (fun p => by simp)
  exact Primrec.list_append.comp hp (Primrec.list_cons.comp
    (terminal_primitive.comp (Primrec.fst.comp Primrec.snd) ho) hi)

theorem build_primitive : Primrec (fun p : Nat×Nat×List Instruction => build p.1 p.2.1 p.2.2) := by
  have ht := SourceBinaryHalvingTrace.Proof.trace_primitive.comp (Primrec.fst (α:=Nat) (β:=Nat×List Instruction))
  exact buildBits_primitive.comp ((Primrec.list_reverse.comp (Primrec.snd.comp ht)).pair
    ((Primrec.fst.comp ht).pair ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))))

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨advance_primitive,buildBits_primitive,build_primitive⟩
end LogicLineages.OrdinalComparison.Source.SourceBinarySpineCode.Proof
