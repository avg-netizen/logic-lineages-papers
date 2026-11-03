module
public import LogicLineages.OrdinalComparison.LayeredComparison.HeterogeneousHeadTargets
public import LogicLineages.OrdinalComparison.HeadEndpointProof
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.HeterogeneousHead.Proof
open CommonHeadLargeRow

theorem actualBand:Targets.ActualHeadBand:=by
  intro rho hlim t ht
  have hi:=actualHeadInputFacts rho.1.repr (rawNotation_repr_lt_epsilonZero rho.1) hlim t ht
  have hb:=actualInfiniteValueEndpointBand (actualHeadInitial rho.1.repr t) hi.1 hi.2.1
  dsimp only at hb
  rw [hi.2.2] at hb
  change actualHeadEndpoint rho.1.repr t=Phi (predecessorIndex rho.1.repr t)∧
    actualHeadEndpoint rho.1.repr t<actualHeadValue rho.1.repr t∧
    actualHeadValue rho.1.repr t<2*actualHeadEndpoint rho.1.repr t∧
    2*actualHeadEndpoint rho.1.repr t<Phi (predecessorIndex rho.1.repr t+1) at hb
  have hp:t≤predecessorIndex rho.1.repr t:=
    iterate_self_le (fun x=>(self_lt_Phi x).le) _ _
  exact ⟨hp,hb.1,hb.1 ▸ hb.2.1,hb.1 ▸ hb.2.2.1⟩

theorem inputExpansive:Targets.ActualInputExpansiveness:=by
  intro rho hlim t ht
  have hb:=actualBand rho hlim t ht
  exact hb.1.trans_lt ((self_lt_Phi _).trans hb.2.2.1)
end LogicLineages.OrdinalComparison.LayeredComparison.HeterogeneousHead.Proof
