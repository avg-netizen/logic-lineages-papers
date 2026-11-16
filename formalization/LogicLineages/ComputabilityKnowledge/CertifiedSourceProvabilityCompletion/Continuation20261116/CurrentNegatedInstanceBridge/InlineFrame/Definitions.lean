module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.Preflight
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame
open GorbowSyntax GorbowPRDefiningEquations SixSol20261113 List.Vector
open LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261115
def frameTerm {ctx : Nat} (ptag atag ltag rtag : Nat) (prefixCode state : Term ctx) : Term ctx :=
 HistoryKernel.pairCall ptag (call ltag (state ::ᵥ nil))
  (HistoryAppend.appendCall atag prefixCode (call rtag (state ::ᵥ nil)))
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.Continuation20261116.CurrentNegatedInstanceBridge.InlineFrame
