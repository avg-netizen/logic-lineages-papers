module
public import LogicLineages.OrdinalComparison.OriginalScaleCompilerCodeTargets
public import LogicLineages.OrdinalComparison.NumericCarrierDataProof
public import LogicLineages.OrdinalComparison.TrackedSourceInspectionCodeProof
public import LogicLineages.OrdinalComparison.WWDefaultSourceAssignmentProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode.Proof
open HeterogeneousUnaryAssembly OriginalScaleFlatList NumericUnaryChain

theorem exactCallerCode : Targets.ExactCallerCode := by
  intro k Γ C u hu
  have hc := (SyntaxCode.Proof.typedCheckExact Γ (Ty.curriedGround (k+1)) (SyntaxCode.encodeTerm C)).mpr ⟨C,rfl⟩
  have ha := (TrackedSourceInspectionCode.Proof.exactArity (Ty.curriedGround (k+1)) (k+1)).mpr rfl
  have hv := DefaultSourceAssignment.Proof.assignmentCorrect Γ (Ty.curriedGround (k+1)) C
  rw [hu,Option.map_some] at hv
  simp only [callerCode,hc,bind,pure,Option.bind_some,↓reduceIte,ha,Nat.add_sub_cancel,
    Nat.add_eq_zero_iff,Nat.one_ne_zero,and_false,↓reduceIte,hv]
  rw [NumericCarrierData.Proof.saturate_source,NumericCarrierData.Proof.saturate_vector]

theorem exactPaidList : Targets.ExactPaidList := by
  intro Γ b xs caller c
  constructor
  · simp [paidCode,paidList,scale,List.map_append,List.map_flatten,List.map_replicate]
  · simp [gapCode,gap,scale]
end LogicLineages.OrdinalComparison.Source.OriginalScaleCompilerCode.Proof
