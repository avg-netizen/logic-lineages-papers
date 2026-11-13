module
public import LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.AxiomProof
public meta import LogicLineages.Audit
@[expose] public section
namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.Proof
open GorbowPRProgram HistoryDispatcher SaturatedDispatcherFuel.IndependenceProof SaturatedDispatcherFuel.PreservationProof

theorem rulePreserves (logical arithmetic : Program 1) (x : Program 3) :
 Preserves (ruleDispatcher logical arithmetic (SaturatedAxiomLeaf.saturated x)) :=
 ruleSelectPreserves 0 (independentPreserves (unaryLeafIndependent logical))
  (ruleSelectPreserves 1 (independentPreserves (unaryLeafIndependent arithmetic))
   (ruleSelectPreserves 2 (independentPreserves mpIndependent)
    (ruleSelectPreserves 3 (independentPreserves generalizationIndependent)
     (ruleSelectPreserves 4 (AxiomProof.axiomPreserves x)
      (independentPreserves (constantIndependent 0))))))

theorem internalMonotonicity : Targets.InternalMonotonicity := by
 intro valid logical arithmetic x
 exact conjunctionPreserves (unaryLeafIndependent valid) (rulePreserves logical arithmetic x)
end LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.Proof
#audit_namespace LogicLineages.ComputabilityKnowledge.CertifiedSourceProvabilityCompletion.SixSol20261113.SaturatedDispatcherFuel.Proof
