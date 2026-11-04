module
public import LogicLineages.OrdinalComparison.SourcePlanInsertionCodeTargets
public import LogicLineages.OrdinalComparison.ContextInsertionCodePrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode.Proof
open SourcePlanSpineCode

theorem port_primitive : Primrec (fun p : Nat×Nat×Nat => portInsert p.1 p.2.1 p.2.2) := by
  have hp : Primrec (fun p : Nat×Nat×Nat => p.2.2) := Primrec.snd.comp Primrec.snd
  exact Primrec.ite (Primrec.eq.comp hp (Primrec.const 0)) (Primrec.const 0)
    (Primrec.ite (Primrec.nat_lt.comp (Primrec.nat_sub.comp hp (Primrec.const 1)) Primrec.fst) hp
      (Primrec.nat_add.comp hp (Primrec.fst.comp Primrec.snd)))
attribute [local irreducible] portInsert

theorem instruction_primitive : Primrec (fun p : Nat×Nat×Instruction => instruction p.1 p.2.1 p.2.2) := by
  have hd : Primrec (fun p : Nat×Nat×Instruction => p.1) := Primrec.fst
  have hk : Primrec (fun p : Nat×Nat×Instruction => p.2.1) := Primrec.fst.comp Primrec.snd
  have hi : Primrec (fun p : Nat×Nat×Instruction => p.2.2) := Primrec.snd.comp Primrec.snd
  have ht := Primrec.fst.comp hi
  have ha := Primrec.fst.comp (Primrec.snd.comp hi)
  have hb := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp hi))
  have hc := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp hi))
  have sa := port_primitive.comp (hd.pair (hk.pair ha))
  have sb := port_primitive.comp (hd.pair (hk.pair hb))
  have sc := port_primitive.comp (hd.pair (hk.pair hc))
  have ea := ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp (hd.pair (hk.pair ha))
  have eb := ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp (hd.pair (hk.pair hb))
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) ((Primrec.const 0).pair (ea.pair (eb.pair hc)))
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) ((Primrec.const 1).pair (sa.pair (sb.pair hc)))
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) ((Primrec.const 2).pair (sa.pair (sb.pair sc)))
        (Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) ((Primrec.const 3).pair (sa.pair (hb.pair hc))) hi)))
attribute [local irreducible] instruction

theorem insert_primitive : Primrec (fun p : Nat×Nat×List Instruction => insert p.1 p.2.1 p.2.2) := by
  let A := Nat×Nat×List Instruction
  let S := Nat×List Instruction
  have hd : Primrec (fun p : A×(S×Instruction) => p.2.1.1) := Primrec.fst.comp (Primrec.fst.comp Primrec.snd)
  have hk : Primrec (fun p : A×(S×Instruction) => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hi : Primrec (fun p : A×(S×Instruction) => p.2.2) := Primrec.snd.comp Primrec.snd
  have ho : Primrec (fun p : A×(S×Instruction) => p.2.1.2) := Primrec.snd.comp (Primrec.fst.comp Primrec.snd)
  have hn := Primrec.ite (Primrec.eq.comp (Primrec.fst.comp hi) (Primrec.const 4))
    (Primrec.nat_add.comp hd (Primrec.const 1)) hd
  have hs : Primrec (fun p : A×(S×Instruction) => scanStep p.1.2.1 p.2.1 p.2.2) :=
    hn.pair (Primrec.list_cons.comp (instruction_primitive.comp (hd.pair (hk.pair hi))) ho)
  have hf : Primrec (fun p : A => p.2.2.foldl (scanStep p.2.1) (p.1,[])) :=
    Primrec.list_foldl (Primrec.snd.comp Primrec.snd) (Primrec.fst.pair (Primrec.const [])) hs.to₂
  exact Primrec.list_reverse.comp (Primrec.snd.comp hf)

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨port_primitive,instruction_primitive,insert_primitive⟩
end LogicLineages.OrdinalComparison.Source.SourcePlanInsertionCode.Proof
