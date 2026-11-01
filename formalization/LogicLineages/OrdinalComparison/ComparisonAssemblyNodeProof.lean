module
public import LogicLineages.OrdinalComparison.ComparisonAssemblyTargets
public import LogicLineages.OrdinalComparison.RangeRangeNodeProof
public import LogicLineages.OrdinalComparison.RangePositiveNodeProof
public import LogicLineages.OrdinalComparison.ComparisonNodePositiveProof

@[expose] public section
namespace LogicLineages.OrdinalComparison.ComparisonAssembly

private theorem computable_ite {α σ : Type} [Primcodable α] [Primcodable σ]
    {p : α → Prop} [DecidablePred p] {f g : α → σ}
    (hp : PrimrecPred p) (hf : Computable f) (hg : Computable g) :
    Computable (fun a => if p a then f a else g a) := by
  simpa only [Bool.cond_decide] using Computable.cond hp.decide.to_comp hf hg

theorem node_program : Targets.ActualComparisonQueryNodeProgram := by
  have hL : PrimrecPred (fun p : ComparisonQuery × ComparisonNodeTable => p.1.1.1%2=0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.fst.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 2)) (Primrec.const 0)
  have hR : PrimrecPred (fun p : ComparisonQuery × ComparisonNodeTable => p.1.1.2%2=0) :=
    Primrec.eq.comp (Primrec.nat_mod.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.fst)) (Primrec.const 2)) (Primrec.const 0)
  exact computable_ite hL
    (computable_ite hR ComparisonNode.positive_node_program.2.2 RangePositiveNode.program.2)
    (computable_ite hR RangePositiveNode.program.2 RangeRangeNode.program.2)

private theorem positive_mod (E : FixedLimitPositiveExpr) : oneVariableComparisonEncode (.positive E)%2=0 := by
  change (2*positiveExprEncode E)%2=0
  omega

private theorem range_mod (w : List (NONote × Nat)) (E : FixedLimitPositiveExpr) :
    oneVariableComparisonEncode (.range w E)%2=1 := by
  change (2*Nat.pair _ _+1)%2=1
  omega

theorem node_correct : Targets.ActualComparisonQueryNodeCorrect := by
  rintro ⟨⟨n,m⟩,⟨leftProfile,rightProfile⟩⟩ table hc E F hEc hFc hE hF
  dsimp only at hEc hFc
  subst n m
  cases E with
  | positive E =>
    cases F with
    | positive F =>
      simpa only [encodedComparisonQueryNode,positive_mod,if_true] using
        ComparisonNode.positive_correct E F hE hF leftProfile rightProfile table hc _ _ rfl rfl hE hF
    | range w F =>
      simpa only [encodedComparisonQueryNode,positive_mod,range_mod,Nat.one_ne_zero,if_true,if_false] using
        RangePositiveNode.positive_range_correct w E F hE hF leftProfile rightProfile table hc _ _ rfl rfl hE hF
  | range w E =>
    cases F with
    | positive F =>
      simpa only [encodedComparisonQueryNode,positive_mod,range_mod,Nat.one_ne_zero,if_true,if_false] using
        RangePositiveNode.range_correct w E F hE hF leftProfile rightProfile table hc _ _ rfl rfl hE hF
    | range v F =>
      simpa only [encodedComparisonQueryNode,range_mod,Nat.one_ne_zero,if_false] using
        RangeRangeNode.correct w v E F hE hF leftProfile rightProfile table hc _ _ rfl rfl hE hF

end LogicLineages.OrdinalComparison.ComparisonAssembly
