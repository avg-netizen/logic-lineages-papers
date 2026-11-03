module
public import LogicLineages.OrdinalComparison.NumericUnaryChainMergeProof
public import LogicLineages.OrdinalComparison.NumericUnaryChainPrimitiveProof
public import LogicLineages.OrdinalComparison.ContextInsertionCodeSemanticProof
public import LogicLineages.OrdinalComparison.HeterogeneousUnaryAssemblyProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.Source.NumericUnaryChain.Proof

theorem exactSingleLambda : Targets.ExactSingleLambda := by
  intro Γ vs
  have hw (v : OriginalTerm Γ (Ty.curriedGround 1)) :
      ContextInsertionCode.sourceCode 0 1 (SyntaxCode.encodeTerm v) =
        SyntaxCode.encodeTerm (v.rename (Renaming.weaken Γ .ground)) :=
    ContextInsertionCode.Proof.exactSourceInsertion [] [.ground] Γ _ v
  have hb : bodyCode (vs.map SyntaxCode.encodeTerm) = SyntaxCode.encodeTerm (SourceUnaryChain.chainBody vs) := by
    induction vs with
    | nil => rfl
    | cons v vs ih =>
      change 8*Nat.pair (ContextInsertionCode.sourceCode 0 1 (SyntaxCode.encodeTerm v))
        (bodyCode (vs.map SyntaxCode.encodeTerm))+5 =
        8*Nat.pair (SyntaxCode.encodeTerm (v.rename (Renaming.weaken Γ .ground)))
          (SyntaxCode.encodeTerm (SourceUnaryChain.chainBody vs))+5
      rw [hw,ih]
  refine ⟨hb,?_⟩
  change 8*Nat.pair 0 (bodyCode (vs.map SyntaxCode.encodeTerm))+6 =
    8*Nat.pair 0 (SyntaxCode.encodeTerm (SourceUnaryChain.chainBody vs))+6
  rw [hb]

theorem actualCompiledChain : Targets.ActualCompiledChain := by
  intro Γ ops
  obtain ⟨v,hv,hval⟩ := HeterogeneousUnaryAssembly.Proof.actualMergedChain Γ ops
  refine ⟨v,?_,hv,hval⟩
  have hm := exactMergedPayloads Γ ops
  have ht : ((HeterogeneousUnaryAssembly.merged ops).map pairCode).map Prod.fst =
      (HeterogeneousUnaryAssembly.terms ops).map SyntaxCode.encodeTerm := by
    simp only [HeterogeneousUnaryAssembly.terms,List.map_map]
    rfl
  unfold compileCode
  rw [hm.1,hm.2.2,ht,(exactSingleLambda _ _).2]
  let t : OriginalTerm (HeterogeneousUnaryAssembly.context ops) (.arrow .ground .ground) :=
    SourceUnaryChain.chainSource (HeterogeneousUnaryAssembly.terms ops)
  have ha : DefaultSourceAssignment.assignmentCode
      ((HeterogeneousUnaryAssembly.context ops).map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t) =
      some (OrdinalSyntax.vectorCode v) := by
    rw [DefaultSourceAssignment.Proof.assignmentCorrect]
    change (AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t).map OrdinalSyntax.vectorCode = _
    rw [show AdmissibleAssignment.assignment OrdinalSyntax.defaultPolicy t = some v from hv]
    rfl
  change ((DefaultSourceAssignment.assignmentCode
    ((HeterogeneousUnaryAssembly.context ops).map SyntaxCode.typeCode) (SyntaxCode.encodeTerm t)).bind
    (fun w => some ((HeterogeneousUnaryAssembly.context ops).map SyntaxCode.typeCode,SyntaxCode.encodeTerm t,w))) = _
  rw [ha]
  rfl
end LogicLineages.OrdinalComparison.Source.NumericUnaryChain.Proof
