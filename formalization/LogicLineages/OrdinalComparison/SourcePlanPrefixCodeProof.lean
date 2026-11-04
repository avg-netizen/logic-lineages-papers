module
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeEmbeddingProof
public import LogicLineages.OrdinalComparison.SourcePlanPrefixCodeCalibrationProof
public import LogicLineages.OrdinalComparison.ContextInsertionCodePrimitiveProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode.Proof

theorem uniformPrimitiveRecursive : Targets.UniformPrimitiveRecursive := by
  have hl : Primrec (fun p : Nat×(Nat×Nat) => ContextInsertionCode.sourceCode 0 p.1 p.2.1) :=
    ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp
      ((Primrec.const 0).pair (Primrec.fst.pair (Primrec.fst.comp Primrec.snd)))
  have hr : Primrec (fun p : Nat×(Nat×Nat) => ContextInsertionCode.sourceCode 0 p.1 p.2.2) :=
    ContextInsertionCode.Proof.primitiveRecursiveAlgorithms.1.comp
      ((Primrec.const 0).pair (Primrec.fst.pair (Primrec.snd.comp Primrec.snd)))
  have hp : Primrec (fun p : Nat×(Nat×Nat) => shiftPair p.1 p.2) := hl.pair hr
  refine ⟨hp,?_⟩
  exact Primrec.list_map Primrec.snd
    (hp.comp ((Primrec.fst.comp Primrec.fst).pair Primrec.snd)).to₂
end LogicLineages.OrdinalComparison.Source.SourcePlanPrefixCode.Proof
