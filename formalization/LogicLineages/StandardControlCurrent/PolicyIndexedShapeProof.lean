module
public import LogicLineages.StandardControlCurrent.PolicyIndexedShapeTargets
import LogicLineages.StandardControlCurrent.PolicyShapeProgramsProof

@[expose] public section
namespace LogicLineages.StandardControlCurrent.PolicyIndexedShape
open OrdinalComparison.Source.AdmissibleSum (Policy)
open Nat.Partrec (Code)
open PolicyShapeProgramsProof (expandProgram)

private theorem inputPrimitive : Primrec (fun p : MacroArgs => Nat.pair p.2.1 p.2.2.1) := by
  have tag : Primrec (fun p : MacroArgs => p.2.1) := Primrec.fst.comp Primrec.snd
  have arity : Primrec (fun p : MacroArgs => p.2.2.1) :=
    Primrec.fst.comp (Primrec.snd.comp Primrec.snd)
  exact Primrec₂.natPair.comp tag arity

private theorem runTapeCodeComputable : Computable₂ runTapeCode := by
  let A := List Nat × Nat
  have decode : Computable (fun p : A => Encodable.decode (α := List Bool) p.2) :=
    Computable.decode.comp Computable.snd
  have expand : Computable₂ (fun (p : A) (tape : List Bool) => PolicyShape.expandCode tape p.1) :=
    (expandProgram.to_comp.comp (Computable.snd.pair (Computable.fst.comp Computable.fst))).to₂
  have h : Computable (fun x : A => runTapeCode x.1 x.2) := Computable.option_bind decode expand
  exact h.to₂

theorem policyIndexedShapePartrec : Partrec macroCode := by
  have interpret : Partrec (fun p : MacroArgs => Code.eval p.1 (Nat.pair p.2.1 p.2.2.1)) :=
    Code.eval_part.comp Computable.fst inputPrimitive.to_comp
  have operands : Computable (fun p : MacroArgs => p.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have finish : Computable₂ (fun (p : MacroArgs) (v : Nat) => runTapeCode p.2.2.2 v) :=
    (runTapeCodeComputable.comp (operands.comp Computable.fst) Computable.snd).to₂
  exact Partrec.map interpret finish

theorem exactPolicyIndexedShape : ExactPolicyIndexedShape := by
  intro c p hc tag arity operands
  unfold macroCode
  rw [hc tag arity]
  simp [runTapeCode,PolicyShape.macroCode]

theorem exactPolicyIndexedShapeValues : ExactPolicyIndexedShapeValues := by
  intro c p hc tag arity operands out
  rw [exactPolicyIndexedShape c p hc tag arity operands]
  exact Part.mem_some_iff

theorem exactPolicyIndexedShapeDomain : ExactPolicyIndexedShapeDomain := by
  intro p
  rfl

theorem everyEffectivePolicyHasIndex : EveryEffectivePolicyHasIndex := by
  intro p hp
  have source : Computable (fun n : Nat =>
      Encodable.encode (PolicyShape.selector p n.unpair.1 n.unpair.2)) :=
    Computable.encode.comp (hp.comp Primrec.unpair.to_comp)
  obtain ⟨c,hc⟩ := Code.exists_code.mp (Partrec.nat_iff.mp source.partrec)
  refine ⟨c,?_⟩
  intro tag arity
  rw [hc]
  simp [PFun.coe_val]

end LogicLineages.StandardControlCurrent.PolicyIndexedShape
