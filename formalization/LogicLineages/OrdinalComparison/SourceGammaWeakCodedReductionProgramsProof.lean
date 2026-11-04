module
public import LogicLineages.OrdinalComparison.SourceGammaWeakCodedReductionTargets
public import LogicLineages.OrdinalComparison.SourceMachineQueryCodeProgramsProof
public import LogicLineages.OrdinalComparison.SourceLiteralWeakWrapperCodeProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction.Proof
attribute [local irreducible] SourceMachineQueryCode.request

/-- The generated weak query applies the literal K and I code constructors. -/
theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive := by
  have hq : Primrec (fun p : Nat × Nat => SourceMachineQueryCode.request p.1 p.2) :=
    SourceMachineQueryCode.Proof.request_primitive
  have hn := Primrec.fst.comp hq
  have hk := SourceLiteralWeakWrapperCode.Proof.uniformPrimitiveRecursive.2.comp
    (Primrec.fst.comp (Primrec.snd.comp hq))
  have hi := SourceLiteralWeakWrapperCode.Proof.uniformPrimitiveRecursive.1.comp
    (Primrec.snd.comp (Primrec.snd.comp hq))
  have hr : Primrec₂ request := hn.pair (hk.pair hi)
  exact ⟨hr,SourceMachineQueryCode.Proof.pack_primitive.comp hr⟩
end LogicLineages.OrdinalComparison.Source.SourceGammaWeakCodedReduction.Proof
