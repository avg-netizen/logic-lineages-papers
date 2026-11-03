module
public import LogicLineages.OrdinalComparison.CommonHeadLargeRowDefinitions
public import LogicLineages.OrdinalComparison.HeadWindowDefinitions
@[expose] public section
namespace LogicLineages.OrdinalComparison.LayeredComparison.HeterogeneousHead.Targets
open CommonHeadLargeRow
/-- Actual ordinal semantics for EACH heterogeneous head, including the real
predecessor input and endpoint band. No supplied endpoint/count/band field. -/
def ActualHeadBand:Prop:=∀rho:NONote,Order.IsSuccLimit rho.1.repr→
  ∀t:Nat,actualOrdinalNorm rho.1.repr≤t→
  t≤predecessorIndex rho.1.repr t∧
  actualHeadEndpoint rho.1.repr t=Phi (predecessorIndex rho.1.repr t)∧
  Phi (predecessorIndex rho.1.repr t)<actualHeadValue rho.1.repr t∧
  actualHeadValue rho.1.repr t<2*Phi (predecessorIndex rho.1.repr t)
/-- Required source-support domination step for a genuine norm input.
It is proved from the actual evaluator, not assumed of a source certificate. -/
def ActualInputExpansiveness:Prop:=∀rho:NONote,Order.IsSuccLimit rho.1.repr→
  ∀t:Nat,actualOrdinalNorm rho.1.repr≤t→t<actualHeadValue rho.1.repr t
end LogicLineages.OrdinalComparison.LayeredComparison.HeterogeneousHead.Targets
