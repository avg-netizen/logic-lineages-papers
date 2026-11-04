module
public import LogicLineages.OrdinalComparison.SourcePlanSpineCodeTargets
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeProof
public import LogicLineages.OrdinalComparison.SourcePrimitiveForestCodeProgramsProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.Proof
open SourcePrimitiveForestCode
attribute [local irreducible] shiftPort eqForest addForest oneForest

theorem step_primitive : Primrec (fun p : Instruction × State => step p.1 p.2) := by
  have ht : Primrec (fun p : Instruction × State => p.1.1) := Primrec.fst.comp Primrec.fst
  have hw : Primrec (fun p : Instruction × State => p.2.1) := Primrec.fst.comp Primrec.snd
  have hf : Primrec (fun p : Instruction × State => p.2.2) := Primrec.snd.comp Primrec.snd
  have ha : Primrec (fun p : Instruction × State => p.1.2.1) := Primrec.fst.comp (Primrec.snd.comp Primrec.fst)
  have hb : Primrec (fun p : Instruction × State => p.1.2.2.1) := Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have hc : Primrec (fun p : Instruction × State => p.1.2.2.2) := Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.fst))
  have sa := SourcePrimitiveForestCode.Proof.shift_primitive.comp hw ha
  have sb := SourcePrimitiveForestCode.Proof.shift_primitive.comp hw hb
  have sc := SourcePrimitiveForestCode.Proof.shift_primitive.comp hw hc
  have hs := SourcePlanPrefixCode.Proof.uniformPrimitiveRecursive.2.comp (Primrec.const 9) hf
  have he := hw.pair (Primrec.list_cons.comp
    (SourcePlanPrefixCode.Proof.uniformPrimitiveRecursive.1.comp (hw.pair (ha.pair hb))) hf)
  have hn := Primrec.nat_add.comp (Primrec.const 9) hw
  have hq := hn.pair (Primrec.list_append.comp (SourcePrimitiveForestCode.Proof.eq_primitive.comp sa sb) hs)
  have hd := hn.pair (Primrec.list_append.comp (SourcePrimitiveForestCode.Proof.add_primitive.comp (sa.pair (sb.pair sc))) hs)
  have ho := hn.pair (Primrec.list_append.comp (SourcePrimitiveForestCode.Proof.one_primitive.comp sa) hs)
  have hx := (Primrec.nat_add.comp (Primrec.const 1) hw).pair hf
  exact Primrec.ite (Primrec.eq.comp ht (Primrec.const 0)) he
    (Primrec.ite (Primrec.eq.comp ht (Primrec.const 1)) hq
      (Primrec.ite (Primrec.eq.comp ht (Primrec.const 2)) hd
        (Primrec.ite (Primrec.eq.comp ht (Primrec.const 3)) ho
          (Primrec.ite (Primrec.eq.comp ht (Primrec.const 4)) hx Primrec.snd))))

theorem run_primitive : Primrec run := by
  have hs : Primrec (fun p : List Instruction × Instruction × State => step p.2.1 p.2.2) :=
    step_primitive.comp ((Primrec.fst.comp Primrec.snd).pair (Primrec.snd.comp Primrec.snd))
  exact Primrec.list_foldr Primrec.id (Primrec.const ((0,[]) : State)) hs.to₂

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive :=
  ⟨step_primitive,run_primitive,SourceGammaAggregateCode.Proof.aggregate_primitive.comp (Primrec.snd.comp run_primitive)⟩
end LogicLineages.OrdinalComparison.Source.SourcePlanSpineCode.Proof
