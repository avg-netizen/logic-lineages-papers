module
public import LogicLineages.PermittedControl.ArbitraryFixedHeadCollapseTargets
import LogicLineages.PermittedControl.FixedHeadCollapseGraphCodeProof
import LogicLineages.OrdinalComparison.EncodedDescentProof
import LogicLineages.OrdinalComparison.RawNormCode
import LogicLineages.OrdinalComparison.RawNormalProof

@[expose] public section
namespace LogicLineages.PermittedControl.ArbitraryFixedHeadCollapse
open OrdinalComparison

private theorem transportedPrimitive : Primrec transported := by
  have head : Primrec (Prod.fst : Input → Nat) := Primrec.fst
  have arg : Primrec (Prod.snd : Input → Nat) := Primrec.snd
  have split := Primrec.unpair.comp ((Primrec.nat_iff.mpr rawSplitPrimitiveRecursive).comp head)
  have limit := Primrec.fst.comp split
  have tail := Primrec.snd.comp split
  have norm := (Primrec.nat_iff.mpr rawNormCodePrimitiveRecursive).comp limit
  exact limit.pair (Primrec.nat_add.comp norm (Primrec.nat_add.comp tail arg))

theorem effectivity : Effectivity := by
  refine ⟨transportedPrimitive,?_⟩
  intro f hf
  have head : Primrec (Prod.fst : Input → Nat) := Primrec.fst
  have arg : Primrec (Prod.snd : Input → Nat) := Primrec.snd
  have normal : PrimrecPred (fun p : Input => rawNormalCode p.1 = 1) :=
    Primrec.eq.comp ((Primrec.nat_iff.mpr rawNormalPrimitiveRecursive).comp head) (Primrec.const 1)
  have finite := encodedFiniteAlgorithmsPrimitiveRecursive.1.comp head
  have value := (Primrec.nat_iff.mpr encodedFiniteAlgorithmsPrimitiveRecursive.2).comp head
  have finiteRead : Computable (fun p : Input => some (encodedFiniteValue p.1 + p.2)) :=
    Computable.option_some.comp (Primrec.nat_add.comp value arg).to_comp
  have limitRead := (FixedHeadCollapseGraph.graphEffective f hf).2.comp transportedPrimitive.to_comp
  apply (Computable.cond normal.decide.to_comp
    (Computable.cond finite.to_comp finiteRead limitRead) (Computable.const none)).of_eq
  intro p
  by_cases h : rawNormalCode p.1 = 1 <;> cases hfinite : encodedFiniteTest p.1 <;>
    simp [read,h,hfinite]

end LogicLineages.PermittedControl.ArbitraryFixedHeadCollapse
